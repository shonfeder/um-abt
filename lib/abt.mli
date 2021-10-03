(* Copyright (c) 2021 Shon Feder

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE. *)

(** {1 Overview}

    [um-abt] is a library for constructing and manipulating the abstract syntax
    of languages that use {{!module:Var} variables}.

    [um-abt] provides unifiable abstract binding trees (UABTs). An {b abstract
    binding tree} (ABT) is an {i abstract syntax tree} (AST), enriched with
    constructs to manage variable binding and scope.

    [um-abt] extends ABTs with support for {{!module:Make.Unification} nominal
    unification} (unificaiton modulo ɑ-equivalence).

    {1 Example}

    A succinct example of the typical use of this library can be seen in the
    following implementation of the untyped λ-calculus.

    Define your language's operators:

    {[
     (* Define the usual operators, but without the variables, since we get those free *)
      module O = struct
        type 'a t =
          | App of 'a * 'a
          | Lam of 'a
        [@@deriving eq, map, fold]

        let to_string : string t -> string = function
          | App (l, m) -> Printf.sprintf "(%s %s)" l m
          | Lam abs    -> Printf.sprintf "(λ%s)" abs
      end
    ]}

    (Note the use of {{:https://github.com/ocaml-ppx/ppx_deriving} ppx_deriving}
    to derive most values automatically.)

    Generate your the ABT representing your syntax, and define combinators to
    easily and safely construct terms of your lanugage construct:

    {[
      (* Generate the syntax, which will include a type [t] of the ABTs over the operators **)
      open Abt.Make (O)

      (* Define some constructors to ensure correct construction *)

      let app m n : t =
        (* [op] lifts an operator into an ABT *)
        op (App (m, n))

      let lam x m : t =
        (* ["x" #. scope] binds all free variables named "x" in the [scope] *)
        op (Lam (x #. m))
    ]}

    Define the dynamics of your language (here using the variable substitution
    function [subst], provided by the generated syntax):

    {[
      let rec eval : t -> t =
        fun t ->
        match t with
        | Opr (App (m, n)) -> apply (eval m) (eval n)
        (* No other terms can be evaluated *)
        | _                -> t

      and apply : t -> t -> t =
        fun m n ->
        match m with
        | Bnd (bnd, t)  -> subst bnd ~value:n t
        | Opr (Lam bnd) -> eval (apply bnd n)
        (* otherwise the application can't be evaluated *)
        | _             -> app m n
    ]}

    Enjoy unification and ɑ-equivalence:

    {[
      (* An example term *)
      let k = lam "x" (lam "y" x)

      (* The generated [Syntax] module includes a [Unification] submodule

         - the [=?=] operator checks for unifiability
         - the [=.=] operator gives an [Ok] result with the unified term, if its operands unify,
           or else an [Error] indicating why the unification failed
         - the [unify] function is like [=.=], but it also gives the substitution used to produce
           a unified term *)
      let ((=?=), (=.=), unify) = Unification.((=?=), (=.=), unify) in

      (* A free variable will unify with anything *)
      assert (v "X" =?= s);

      (* Unification is modulo ɑ-equivalence *)
      assert (lam "y" (lam "x" y) =?= lam "x" (lam "y" x));

      (* Here we unify the free variable "M" with the body of the [k] combinator,
         note that the nominal unification is modulo bound variables: *)
      let unified_term = (lam "z" (v "M") =.= k) |> Result.get_ok in
      assert (to_string unified_term = "(λz.(λy.z))");
    ]}
*)

(** {1 Modules and interfaces} *)

(** The interface for a module that defines the operators of a language *)
module type Operator = sig
  type 'a t [@@deriving sexp]
  (** The type of the operator, usually represented as a sum type.

      Each operator should be have the form

      {[
        Foo of 'a * 'a * ... * 'a
      ]}

      Where the free variables ['a] are arguments to the operator [Foo]. *)

  val map : ('a -> 'b) -> 'a t -> 'b t

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a

  val to_string : string t -> string
end

(** Variables, named by strings, which can be bound to a {!module:Var.Binding} or
    left free. *)
module Var : sig
  (** A binding is an immutable reference, to which a bound can refer. *)
  module Binding : sig
    include Map.OrderedType

    val equal : t -> t -> bool

    val v : string -> t
    (** [binding s] is a new binding for variables named [s] *)

    val name : t -> string
  end

  type t = private
    | Free of string
    | Bound of Binding.t  (** A varibale of type [t] is either free or bound. *)
  [@@deriving sexp]

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

  val to_string_debug : t -> string
  (** Includes the unique ID of any bound variables *)

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

(** The interface of the family of UABTs representings a syntax *)
module type Syntax = sig
  module Op : Operator

  (** The type of ABT's constructed from the operators defind in [O] *)
  type t = private
    | Var of Var.t  (** Variables *)
    | Bnd of Var.Binding.t * t  (** Scoped variable binding *)
    | Opr of t Op.t  (** Operators specified in {!Op} *)

  val bind : Var.Binding.t -> t -> t
  (** [bind bnd t] is a branch of the ABT, in which any free variables in [t]
      matching the name of [bnd] are bound to [bnd].  *)

  val of_var : Var.t -> t
  (** [of_var v] is a leaf in the ABT consisting of the variable [v] *)

  val v : string -> t
  (** [v x] is a leaf in the ABT consisting of a variable named [x] *)

  val op : t Op.t -> t
  (** [op o] is a branch in the ABT consisting of the operator [o]  *)

  val ( #. ) : string -> t -> t
  (** [x #. t] is a new abt obtained by binding all {i free} variables named
      [x] in [t]

      Note that this does {b not} substitute variables for a {i value}, (for
      which, see {!subst}). This only binds the free variables within the scope
      of an abstraction that ranges over the given (sub) abt [t]. *)

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
    -> opr:(t Op.t -> 'a)
    -> t
    -> 'a
  (** Case analysis for eleminating ABTs

      This is an alternative to using pattern-based elimination.

      @param var function to apply to variables
      @param bnd function to apply to bindings
      @param opr function to apply to operators *)

  val subterms : t -> t list
  (** [subterms t] is a list of all the subterms in [t], including [t] itself *)

  val free_vars : t -> Var.Set.t
  (** [free_vars t] is the set of variables that are free in in [t] *)

  val is_closed : t -> bool
  (** [is_closed t] if [true] if there are no free variables in [t], otherwise false *)

  module Unification : sig
    module Subst : sig
      type term = t
      (** An alias for the type of the ABT for reference in the context of the substitution *)

      type t
      (** Substitutions mapping free variables to terms *)

      val find : Var.t -> t -> term option
      (** [find v s] is [Some term] if [v] is bound to [term] in the
          substitution [s], otherwise it is [None]*)

      val bindings : t -> (Var.t * term) list
      (** [bindings s] is a list of all the bindings in [s] *)

      val to_string : t -> string
    end

    type error =
      [ `Unification of Var.t option * t * t
      | `Occurs of Var.t * t
      | `Cycle of Subst.t
      ]
    (** Errors returned when unification fails *)

    val unify : t -> t -> (t * Subst.t, error) Result.t
    (** [unify a b] is [Ok (union, substitution)] when [a] and [b] can be
        unified into the term [union] and [substitution] is the most general
        unifier. Otherwise it is [Error err)], for which, see {!type:error} *)

    val ( =.= ) : t -> t -> (t, error) Result.t
    (** [a =.= b] is [unify a b |> Result.map fst] *)

    val ( =?= ) : t -> t -> bool
    (** [a =?= b] is [true] iff [a =.= b] is an [Ok _] value *)
  end
end

(** [Make (Op)] is a module for constructing and manipulating the
    {!module:Syntax} of a language with {!module:Operator}s defined by [Op]. *)
module Make (Op : Operator) : Syntax with module Op = Op
