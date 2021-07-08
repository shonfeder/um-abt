module Var : sig
  (** Variables, named by strings, which can be bound to a {!module:Binding} or
      left free. *)

  type t
  (** A varibale of type [t] is either free or bound. *)

  module Binding : sig
    (** A binding is an immutable reference to which a variable can be bound. *)

    include Map.OrderedType

    val equal : t -> t -> bool

    val v : string -> t
    (** [binding s] is a new binding for variables named [s] *)

    val name : t -> string
  end

  val compare : t -> t -> int
  (** Bound variables are equal if they are have the same binding, free
      variables are greater than bound variables, and variables are otherwise
      compared lexigraphically by name.

      Specifically,

      [compare a b] is [0] iff

      - [is_free a && is_free b] and [name a = name b]
      - [is_bound a && is_bound b] and both [a] and [b] are bound to the same
        {!type:binding} by way of {!val:bind}.

      [compare a b] is [String.compare (name a) (name b)] if
      [is_free a && is_free b] or [is_bound a && is_bound b].

      [compare a b] is -1 if [is_bound a] and [is_free b] or 1 if [is_free a]
      and [is_bound b] *)

  val equal : t -> t -> bool
  (** [equal a b] is [true] iff

      - [is_free a && is_free b] and [name a = name b]
      - [is_bound a && is_bound b] and both [a] and [b] are bound to the same
        {!type:binding} by way of {!val:bind}. *)

  val is_free : t -> bool

  val is_bound : t -> bool

  val v : string -> t

  val to_string : t -> string

  val name : t -> string
  (** [name v] is [to_string v] *)

  val bind : t -> Binding.t -> t option
  (** [bind v bnd] is [Some var] when [is_free v] and [name v = Binding.name bnd],
      where [var] is a new variable with the same name but bound to [bnd].
      Otherwise, it is [None].

      See {!val:equal}. *)

  val is_bound_to : t -> Binding.t -> bool
  (** [is_bound_to v bnd] is [true] if [v] is bound to [bnd], via {!val:bind} *)

  val of_binding : Binding.t -> t
  (** [of_binding bnd] is a variable bound to [bnd] *)

  val to_binding : t -> Binding.t option
  (** [to_binding v] is [Some bnd] iff [v] is bound to [bnd] via {!val:bind}.
      Otherwise it is [None]. *)
end = struct
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

  type t =
    | Free of string
    | Bound of Binding.t

  let compare a b =
    match (a, b) with
    | Bound a, Bound b -> Binding.compare a b
    | Free a, Free b   -> String.compare a b
    | Free _, Bound _  -> 1 (* Free vars are greater than bound vars *)
    | Bound _, Free _  -> -1

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
end

module Make (O : Operator) : sig
  (** [Make (O)] is a module for constructing and manipulating ABTs for the
      operators defined in [O]. *)

  type t
  (** The type of ABT's constructed from the operators defind in [O] *)

  val v : string -> t
  (** [v x] is a leaf in the ABT consisting of a variable named [x] *)

  val op : t O.t -> t
  (** [op o] is a branch in the ABT consisting of the operator [o]  *)

  val ( #. ) : string -> t -> t
  (** [x #. t] is a new abt obtained by binding all {i free} variables named
      [x] in [t]

      Note that this does {b not} bind the variables to a {i value}, (for which,
      see {!subst}). This only binds the free variables within the scope of an
      abstraction that ranges over the given (sub) abt [t]. *)

  val subst : string -> value:t -> t -> t
  (** [subst name ~value t] is a new abt obtained by substituting [value] for
      the outermost scope of variables bound to [name] in [t] *)

  val to_string : t -> string
  (** [to_string t] is the representation of [t] as a string *)

  val equal : t -> t -> bool
  (** [equal t t'] is [true] when [t] and [t'] are alpha equivalent and [false] otherwise *)

  val case :
       var:(Var.t -> 'a)
    -> bnd:(Var.Binding.t -> t -> 'a)
    -> opr:(t O.t -> 'a)
    -> t
    -> 'a

  val transform :
       var:(Var.t -> Var.t)
    -> bnd:(Var.Binding.t * t -> Var.Binding.t * t)
    -> opr:(t O.t -> t O.t)
    -> t
    -> t
end = struct
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

  let rec subst_val : Var.Binding.t -> value:t -> t -> t =
   fun bnd ~value ->
    app_t @@ function
    | Opr op     -> Opr (O.map (subst_val bnd ~value) op)
    | Bnd (b, t) ->
        (* As an optimization, we don't go any deeper if the variable is shadowed.
         * We could, safely, but there's no point. *)
        if String.equal (Var.Binding.name b) (Var.Binding.name bnd) then
          Bnd (b, t)
        else
          Bnd (b, subst_val bnd ~value t)
    | Var v      ->
        if Var.is_bound_to v bnd then
          un_t value
        else
          Var v

  let rec subst : string -> value:t -> t -> t =
   fun name ~value ->
    app_t @@ function
    | Var v      -> Var v
    | Opr op     -> Opr (O.map (subst name ~value) op)
    | Bnd (b, t) ->
        if Var.Binding.name b = name then
          un_t (subst_val b ~value t)
        else
          Bnd (b, subst name ~value t)

  let op a = T (Opr a)

  let v : string -> t = fun s -> T (Var (Var.v s))

  let case ~var ~bnd ~opr t =
    match un_t t with
    | Var v      -> var v
    | Bnd (b, t) -> bnd b t
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
end

let%expect_test "Example usage" =
  let module Syntax = struct
    module Operator = struct
      type 'a t =
        | Num of int
        | Plus of 'a * 'a

      let equal eq a b =
        match (a, b) with
        | Num n, Num n'              -> Int.equal n n'
        | Plus (a, b), Plus (a', b') -> eq a a' && eq b b'
        | _                          -> false

      let map f t =
        match t with
        | Num n       -> Num n
        | Plus (a, b) -> Plus (f a, f b)

      let to_string : string t -> string = function
        | Num n       -> Int.to_string n
        | Plus (a, b) -> Printf.sprintf "(%s + %s)" a b
    end

    include Make (Operator)

    let num n = op (Num n)

    let plus a b = op (Plus (a, b))

    let show t = to_string t |> print_endline
  end in
  let module Semantics = struct
    open Syntax

    let rec reduce : t -> int option =
     fun t ->
      let var = Fun.const None in
      let bnd _ = Fun.const None in
      let opr =
        let open Operator in
        function
        | Num n       -> Some n
        | Plus (a, b) ->
        match (reduce a, reduce b) with
        | None, _
        | _, None ->
            None
        | Some a, Some b -> Some (a + b)
      in
      case t ~var ~bnd ~opr

    let rec eval : t -> t =
     fun t ->
      let var = Fun.id in
      let bnd (b, t) = (b, eval t) in
      let opr =
        let open Operator in
        function
        | Num n       -> Num n
        | Plus (a, b) ->
        match (reduce a, reduce b) with
        | None, None      -> Plus (a, b)
        | Some n, Some n' -> Num (n + n')
        | Some n, None    -> Plus (num n, b)
        | None, Some n'   -> Plus (a, num n')
      in
      transform t ~var ~bnd ~opr
  end in
  let one = Syntax.(num 1) in
  Syntax.show one;
  [%expect {| 1 |}];

  let two = Syntax.(num 2) in
  Syntax.show two;
  [%expect {| 2 |}];

  let one_plus_x = Syntax.(plus one (v "x")) in
  Syntax.show one_plus_x;
  [%expect {| (1 + x) |}];

  let one_plus_y = Syntax.(plus one (v "y")) in
  Syntax.show one_plus_y;
  [%expect {| (1 + y) |}];

  (* Free variables are not alpha equivalent  *)
  assert (Syntax.(not @@ equal one_plus_x one_plus_y));

  let shadow_x_in_bound_x = Syntax.("x" #. (plus "x"#.one_plus_x (v "x"))) in
  Syntax.show shadow_x_in_bound_x;
  [%expect {| x.(x.(1 + x) + x) |}];

  let bind_x_in_bound_y = Syntax.("y" #. (plus "x"#.one_plus_x (v "y"))) in
  Syntax.show bind_x_in_bound_y;
  [%expect {| y.(x.(1 + x) + y) |}];

  (* Bound variables allow alpha equivalence *)
  assert (Syntax.(equal shadow_x_in_bound_x bind_x_in_bound_y));

  (* Substitution respects shadowed scope *)
  let subst1 = Syntax.(shadow_x_in_bound_x |> subst "x" ~value:(num 3)) in
  Syntax.show subst1;
  [%expect {| (x.(1 + x) + 3) |}];

  (* Subsequent substitution works as expected *)
  Syntax.(subst1 |> subst "x" ~value:(num 4) |> show);
  [%expect {| ((1 + 4) + 3) |}];

  (* Substitution does not mutate abts, so we can give alternate assignments to
     previously defined trees. *)
  let fully_bound = Syntax.(subst1 |> subst "x" ~value:(num 99)) in
  Syntax.show fully_bound;
  [%expect {| ((1 + 99) + 3) |}];

  Semantics.eval fully_bound |> Syntax.show;
  [%expect {| 103 |}];

  Semantics.eval Syntax.(subst "x" ~value:(num 4) bind_x_in_bound_y) |> Syntax.show;
  [%expect {| y.(5 + y) |}];
