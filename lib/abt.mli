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

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end

module type Operator = sig
  (** An operator *)

  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t

  val to_string : string t -> string

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
end

module Make (O : Operator) : sig
  (** [Make (O)] is a module for constructing and manipulating ABTs for the
      operators defined in [O]. *)

  type t
  (** The type of ABT's constructed from the operators defind in [O] *)

  val of_var : Var.t -> t
  (** [of_var v] is a leaf in the ABT consisting of the variable [v] *)

  val bind : Var.Binding.t -> t -> t
  (** [bind bnd t] is a branch of the ABT, in which any free variables in [t]
      matching the name of [bnd] are bound to [bnd].  *)

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

  val subst : Var.Binding.t -> value:t -> t -> t
  (** [subst bnd ~value t] is a new ABT obtained by substituting [value] for
      all variables bound to [bnd]. *)

  val subst_var : string -> value:t -> t -> t
  (** [subst_var name ~value t] is a new abt obtained by substituting [value] for
      the outermost scope of variables bound to [name] in [t] *)

  val to_string : t -> string
  (** [to_string t] is the representation of [t] as a string *)

  val equal : t -> t -> bool
  (** [equal t t'] is [true] when [t] and [t'] are alpha equivalent and [false] otherwise *)

  val case :
       var:(Var.t -> 'a)
    -> bnd:(Var.Binding.t * t -> 'a)
    -> opr:(t O.t -> 'a)
    -> t
    -> 'a
  (** Case analysis for eleminating the terms of the ABT
   *
   *  The usual use case is for implementing the dynamics of the language whose
   *  statics are defined by the ABT.
   *
   *  For examples, see test/example/example.ml
   *
   *  @param var function to apply to variables
   *  @param bnd function to apply to bindings
   *  @param opr function to apply to operators
   *)

  val transform :
       var:(Var.t -> Var.t)
    -> bnd:(Var.Binding.t * t -> Var.Binding.t * t)
    -> opr:(t O.t -> t O.t)
    -> t
    -> t
  (** Case anslysis for transforming ABT
   *)

  val free_vars : t -> Var.Set.t
  (** [free_vars t] is the set of variables that are free in in [t] *)

  val is_closed : t -> bool
  (** [is_closed t] if [true] if there are no free variables in [t], otherwise false *)
end
