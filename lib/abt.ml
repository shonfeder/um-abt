module Var = struct
  module Binding = struct
    type t = string ref

    let v s = ref s

    let name bnd = !bnd

    let compare a b =
      if a == b then
        0
      else
        String.compare !a !b

    let equal a b = Int.equal (compare a b) 0
  end

  module T = struct
    type t =
      | Free of string
      | Bound of Binding.t

    let compare a b =
      match (a, b) with
      | Bound a, Bound b -> Binding.compare a b
      | Free a, Free b   -> String.compare a b
      | Free _, Bound _  -> 1 (* Free vars are greater than bound vars *)
      | Bound _, Free _  -> -1
  end

  module Set = Set.Make (T)
  module Map = Map.Make (T)
  include T

  let equal a b = Int.equal (compare a b) 0

  let is_free = function
    | Free _ -> true
    | _      -> false

  let is_bound t = not (is_free t)

  let name = function
    | Free s  -> s
    | Bound b -> !b

  let to_string = name

  let v s = Free s

  let bind v b =
    match v with
    | Bound _   -> None
    | Free name ->
        if name = !b then
          Some (Bound b)
        else
          None

  let of_binding b = Bound b

  let to_binding = function
    | Bound b -> Some b
    | Free _  -> None

  let is_bound_to v bnd =
    match v with
    | Free _  -> false
    | Bound b -> b == bnd
end

module type Operator = sig
  (** An operator *)

  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t

  val to_string : string t -> string

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
end

module Make (O : Operator) = struct
  type abt =
    | Var of Var.t
    | Bnd of Var.Binding.t * t
    | Opr of t O.t

  and t = T of abt

  (* Get the ABT inside of t *)
  let un_t : t -> abt = fun (T abt) -> abt

  (* Put the ABT inside of t *)
  let in_t : abt -> t = fun abt -> T abt

  (* Apply f to the ABT inside of t *)
  let app_t : (abt -> abt) -> t -> t = fun f t -> un_t t |> f |> in_t

  (* Alpha-equivalence is derived by checking that the structure of the
     two abts is the same.

     - For operators, this just amounts to checking the equality supplied by the
       given {!modtype:Operator}, [O].
     - For variable, we check that the pointer {i structure} is equivalent, and
       do take no account of names, since alpha equivalence is fundamentally
       concerned with the (anonymous) binding structure of ABTs. *)
  let equal : t -> t -> bool =
    let module Bindmap = Map.Make (Var.Binding) in
    let vars_equal bimap x x' =
      match Var.(to_binding x, to_binding x') with
      | Some _, None    -> false
      | None, Some _    -> false
      | None, None      -> Var.equal x x'
      | Some b, Some b' ->
      (* Two bound variables are equal when their bindings correspond *)
      match Bindmap.find_opt b bimap with
      | Some b'' -> Var.Binding.equal b' b''
      | None     -> false
    in
    let rec equal : Var.Binding.t Bindmap.t -> t -> t -> bool =
     fun bimap t t' ->
      match (un_t t, un_t t') with
      | Opr o, Opr o'            -> O.equal (equal bimap) o o'
      | Bnd (b, t), Bnd (b', t') ->
          (* Associate corresponding bindings in a bimap *)
          equal (Bindmap.add b b' bimap) t t'
      | Var x, Var x'            -> vars_equal bimap x x'
      | _                        -> false
    in
    fun a b -> equal Bindmap.empty a b

  let rec to_string t =
    un_t t |> function
    | Var v        -> Var.to_string v
    | Bnd (b, abt) -> Var.(name @@ of_binding b) ^ "." ^ to_string abt
    | Opr op       -> O.map to_string op |> O.to_string

  let of_var : Var.t -> t = fun v -> in_t (Var v)

  let rec bind : Var.Binding.t -> t -> t =
   fun bnd ->
    app_t @@ function
    | Opr op     -> Opr (O.map (bind bnd) op)
    | Bnd (b, t) -> Bnd (b, bind bnd t)
    | Var v      ->
    match Var.bind v bnd with
    | None    -> Var v
    | Some v' -> Var v'

  let ( #. ) : string -> t -> t =
   fun name abt ->
    let binding : Var.Binding.t = Var.Binding.v name in
    let scope = bind binding abt in
    T (Bnd (binding, scope))

  let rec subst : Var.Binding.t -> value:t -> t -> t =
   fun bnd ~value ->
    app_t @@ function
    | Opr op     -> Opr (O.map (subst bnd ~value) op)
    | Bnd (b, t) ->
        (* As an optimization, we don't go any deeper if the variable is shadowed.
         * We could, safely, but there's no point. *)
        if String.equal (Var.Binding.name b) (Var.Binding.name bnd) then
          Bnd (b, t)
        else
          Bnd (b, subst bnd ~value t)
    | Var v      ->
        if Var.is_bound_to v bnd then
          un_t value
        else
          Var v

  let rec subst_var : string -> value:t -> t -> t =
   fun name ~value ->
    app_t @@ function
    | Var v      -> Var v
    | Opr op     -> Opr (O.map (subst_var name ~value) op)
    | Bnd (b, t) ->
        if Var.Binding.name b = name then
          un_t (subst b ~value t)
        else
          Bnd (b, subst_var name ~value t)

  let op a = T (Opr a)

  let v : string -> t = fun s -> T (Var (Var.v s))

  let case ~var ~bnd ~opr t =
    match un_t t with
    | Var v      -> var v
    | Bnd (b, t) -> bnd (b, t)
    | Opr o      -> opr o

  let transform ~var ~bnd ~opr t =
    in_t
    @@
    match un_t t with
    | Var v      -> Var (var v)
    | Opr o      -> Opr (opr o)
    | Bnd (b, t) ->
        let b, t = bnd (b, t) in
        Bnd (b, t)

  let free_vars : t -> Var.Set.t =
   fun t ->
    let rec free m =
      case
        ~var:(fun v ->
          if Var.is_free v then
            Var.Set.add v m
          else
            m)
        ~bnd:(fun (_, t') -> free m t')
        ~opr:(fun op -> O.fold free m op)
    in
    free Var.Set.empty t

  let is_closed : t -> bool = fun t -> Var.Set.is_empty (free_vars t)
end
