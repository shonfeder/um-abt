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

module Operator_aux (O : Operator) = struct
  (* Adds auxiliary functions over an operator module*)

  (** [same o o'] is [true] if the operators are operators are the same without respect to their
      arguments *)
  let same : 'a O.t -> 'a O.t -> bool =
   fun o o' ->
    let to_unit = O.map (Fun.const ()) in
    O.equal Unit.equal (to_unit o) (to_unit o')

  (* TODO: Construct a lazy/incremental seq instead *)
  let to_list : 'a O.t -> 'a List.t =
   fun o -> O.fold (Fun.flip List.cons) [] o |> List.rev

  let fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b O.t -> 'c O.t -> 'a =
   fun f init o o' ->
    let app (list_o', acc) o =
      match list_o' with
      | []        ->
          raise
            (Invalid_argument "Operator_aux.fold2 on operators of unequal size")
      | o' :: res -> (res, f acc o o')
    in
    O.fold app (to_list o', init) o |> snd

  include O
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

  let is_free_var : t -> bool =
   fun t ->
    match un_t t with
    | Var v -> Var.is_free v
    | _     -> false

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

  module Unification = struct
    (* Initial, naive approach:
     *   1. get all free vars of a and b
     *   1. build mgu and substitute for all vars
     *   3. then check for alpha-equiv
     *
     * Will take 3n complexity
     *
     * TODO To optimize: need to unify on a single pass, which will require way of identifying if two
     * operators have the same head. Perhaps via an operator function `sort : O.t -> (string * int)`? *)

    type error = [ `Unification of Var.t option * t * t ]

    let err ?v t t' : error = `Unification (v, t, t')

    (* Error when a substitution is added for a variable already assigned to an incompatible value *)
    module Subst = struct
      type term = t

      type t = term ref Var.Map.t
      (** Substitution maps free variables to mutable refs.
          When two free variables are assigned to be aliases, they simply share the same ref.
          Therefore, assigning one variable, sufficies to assign all of its aliases. *)

      let empty = Var.Map.empty

      let find v s = Var.Map.find_opt v s |> Option.map (fun x -> !x)

      let bindings s = Var.Map.bindings s |> List.map (fun (v, t) -> (v, !t))

      let to_string s =
        s
        |> bindings
        |> List.map (fun (v, term) ->
               Printf.sprintf "%s -> %s" (Var.to_string v) (to_string term))
        |> String.concat ", "
        |> Printf.sprintf "[ %s ]"

      (* Effect the substitution of free variables in a term, according to the sustitution s
       * - unassigned free var -> free var
       * - assigned free var -> assigned value
       * - compound term -> substitute into each of it's compounds
       * - bound var -> bound var *)
      let rec apply : t -> term -> term =
       fun s term ->
        match un_t term with
        | Bnd (b, t') -> Bnd (b, apply s t') |> in_t
        | Opr o       -> O.map (apply s) o |> op
        | Var v       ->
            if Var.is_bound v then
              of_var v
            else
              Var.Map.find_opt v s
              |> Option.map (fun { contents } ->
                     if not (is_free_var contents) then
                       apply s contents
                     else
                       contents)
              |> Option.value ~default:term

      let add : t -> Var.t -> term -> (t, error) Result.t =
       fun s v term ->
        if not (Var.is_free v) then
          failwith "Invalid argument: Subst.add with non free var "
        else
          match un_t term with
          | Bnd (_, _)
          | Opr _ -> (
              Var.Map.find_opt v s |> function
              | None -> Ok (Var.Map.add v (ref term) s)
              | Some ref_term when equal !ref_term term -> Ok s
              | Some ref_var when is_free_var !ref_var ->
                  ref_var := term;
                  Ok s
              | Some clash_term -> Error (err ~v term !clash_term))
          | Var v' ->
          match (Var.Map.find_opt v s, Var.Map.find_opt v' s) with
          | Some term_ref, None -> Ok (Var.Map.add v' term_ref s)
          | None, Some term_ref' -> Ok (Var.Map.add v term_ref' s)
          | Some term_ref, Some term_ref' ->
              if term_ref == term_ref' then
                Ok s
              else
                Error (err ~v !term_ref !term_ref')
          | None, None ->
              let ref_var = ref (of_var v) in
              Ok (Var.Map.add v ref_var s |> Var.Map.add v' ref_var)
    end

    module O = Operator_aux (O)

    let ( let* ) = Result.bind

    let rec build_substitution s_res a b =
      let* s = s_res in
      match (un_t a, un_t b) with
      | Opr ao, Opr bo when O.same ao bo ->
          O.fold2 build_substitution (Ok s) ao bo
      | Bnd (_, a'), Bnd (_, b') -> build_substitution (Ok s) a' b'
      | Var v, _ -> Subst.add s v b
      | _, Var v -> Subst.add s v a
      | _ -> Error (err a b)

    let unify : t -> t -> (t * Subst.t, error) Result.t =
     fun a b ->
      let* subst = build_substitution (Ok Subst.empty) a b in
      let a' = Subst.apply subst a in
      let b' = Subst.apply subst b in
      if equal a' b' then
        Ok (a', subst)
      else
        Error (err a' b')
  end
end
