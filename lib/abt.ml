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

module Log = Logs

module type Operator = sig
  (** An operator *)

  type 'a t [@@deriving sexp]

  val map : ('a -> 'b) -> 'a t -> 'b t

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a

  val to_string : string t -> string
end

module Var = struct
  module Binding = struct
    (* A private table of the number of times a name has been bound *)
    let bnd_names : (string, int) Hashtbl.t = Hashtbl.create 100

    let name_count n = Hashtbl.find_opt bnd_names n |> Option.value ~default:0

    let add_name n =
      let count = name_count n + 1 in
      Hashtbl.add bnd_names n count;
      count

    open Sexplib.Std

    type t = (string * int) ref [@@deriving sexp]

    let v s = ref (s, add_name s)

    (** Just the string component of the name *)
    let name bnd = !bnd |> fst

    (** Representation of name that includes the unique id *)
    let name_debug bnd =
      let n, c = !bnd in
      n ^ Int.to_string c

    let compare a b =
      (* Physical equality of references *)
      if a == b then
        0
      else
        let a_name, a_count = !a in
        let b_name, b_count = !b in
        let name_cmp = String.compare a_name b_name in
        if name_cmp = 0 then
          Int.compare a_count b_count
        else
          name_cmp

    let equal a b = Int.equal (compare a b) 0
  end

  module T = struct
    open Sexplib.Std

    type t =
      | Free of string
      | Bound of Binding.t
    [@@deriving sexp]

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
    | Bound b -> Binding.name b

  let to_string = name

  let to_string_debug = function
    | Free s  -> s
    | Bound b -> Binding.name_debug b

  let v s = Free s

  let bind v b =
    match v with
    | Bound _   -> None
    | Free name ->
        if String.equal name (Binding.name b) then
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

  (** Derives a fold2 implementation from the required fold *)
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

module Bndmap : sig
  type t

  val empty : t

  val add : left:Var.Binding.t -> right:Var.Binding.t -> t -> t

  type lookup = Var.Binding.t -> t -> Var.Binding.t option

  (* [find bnd m] is the binding corresponding to [bnd], regardless of which
     side it was entered from *)
  (* val find : lookup *)

  (* [find_left bnd m] is [bnd] if [bnd] was entered from the left, otherwise it
     is the left-side binding corresponding to the one entered on the right *)
  val find_left : lookup

  (* [find_left bnd m] is [bnd] if [bnd] was entered from the right, otherwise it
     is the left-side binding corresponding to the one entered on the left *)
  val find_right : lookup
end = struct
  module M = Map.Make (Var.Binding)

  type t =
    { left : Var.Binding.t M.t
    ; right : Var.Binding.t M.t
    }

  let empty = { left = M.empty; right = M.empty }

  let add ~left ~right m =
    { left = M.add left right m.left; right = M.add right left m.right }

  type lookup = Var.Binding.t -> t -> Var.Binding.t option

  (* Var.Binding.t are unique (because identified by pointer location reference)
     so we don't need safety constraints on lookup etc. *)
  (* let find k m =
   *   match M.find_opt k m.left with
   *   | None   -> M.find_opt k m.right
   *   | Some v -> Some v *)

  let find_left k m =
    if M.mem k m.left then
      Some k
    else
      M.find_opt k m.right

  let find_right k m =
    if M.mem k m.right then
      Some k
    else
      M.find_opt k m.left
end

module type Syntax = sig
  module Op : Operator

  (** The type of ABT's constructed from the operators defind in [O] *)
  type t = private
    | Var of Var.t  (** Variables *)
    | Bnd of Var.Binding.t * t  (** Scoped variable binding *)
    | Opr of t Op.t  (** Operators specified in {!Op} *)
  [@@deriving sexp]

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

  val to_sexp : t -> Sexplib.Sexp.t
  (** [to_sexp t] is the representation of [t] as an s-expression *)

  val of_sexp : Sexplib.Sexp.t -> t
  (** [of_sexp s] is Abt represented by the s-expression [s] *)

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

module Make (Op : Operator) = struct
  module Op = Op

  type t =
    | Var of Var.t
    | Bnd of Var.Binding.t * t
    | Opr of t Op.t
  [@@deriving sexp]

  let to_sexp = sexp_of_t
  let of_sexp = t_of_sexp

  let rec to_string t =
    t |> function
    | Var v        -> Var.to_string v
    | Bnd (b, abt) -> Var.(name @@ of_binding b) ^ "." ^ to_string abt
    | Opr op       -> Op.map to_string op |> Op.to_string

  (* Alpha-equivalence is derived by checking that the ABTs are identical
     modulo the pointer structure of any bound variables.

     - For operators, this just amounts to checking the equality supplied by the
       given {!modtype:Operator}, [O].
     - For variable, we check that the pointer {i structure} is equivalent, and
       do take no account of names, since alpha equivalence is fundamentally
       concerned with the (anonymous) binding structure of ABTs. *)
  let equal : t -> t -> bool =
    let bindings_correlated bndmap bnd bnd' =
      match Bndmap.find_right bnd bndmap with
      | Some bnd'' -> Var.Binding.equal bnd' bnd''
      | None       -> false
    in
    let rec equal : Bndmap.t -> t -> t -> bool =
     fun bndmap t t' ->
      [%log debug "check ɑ-equality of %s %s" (to_string t) (to_string t')];
      match (t, t') with
      | Opr o, Opr o' -> Op.equal (equal bndmap) o o'
      | Bnd (left, t), Bnd (right, t') ->
          (* Associate corresponding bindings in the bindmap *)
          equal (Bndmap.add ~left ~right bndmap) t t'
      | Var (Bound bnd), Var (Bound bnd') -> bindings_correlated bndmap bnd bnd'
      | Var v, Var v' -> Var.equal v v'
      | _ -> false
    in
    fun a b -> equal Bndmap.empty a b

  let of_var : Var.t -> t = fun v -> Var v

  let bind : Var.Binding.t -> t -> t =
   fun bnd t ->
    let rec scope = function
      | Opr op     -> Opr (Op.map scope op)
      | Bnd (b, t) -> Bnd (b, scope t)
      | Var v      ->
      match Var.bind v bnd with
      | None    -> Var v
      | Some v' -> Var v'
    in
    Bnd (bnd, scope t)

  let ( #. ) : string -> t -> t =
   fun name abt ->
    let binding : Var.Binding.t = Var.Binding.v name in
    bind binding abt

  let rec subst : Var.Binding.t -> value:t -> t -> t =
   fun bnd ~value -> function
    | Opr op     -> Opr (Op.map (subst bnd ~value) op)
    | Bnd (b, t) ->
        (* As an optimization, we don't go any deeper if the variable is shadowed.
         * We could, safely, but there's no point. *)
        if String.equal (Var.Binding.name b) (Var.Binding.name bnd) then
          Bnd (b, t)
        else
          Bnd (b, subst bnd ~value t)
    | Var v      ->
        if Var.is_bound_to v bnd then
          value
        else
          Var v

  let rec subst_var : string -> value:t -> t -> t =
   fun name ~value -> function
    | Var v      -> Var v
    | Opr op     -> Opr (Op.map (subst_var name ~value) op)
    | Bnd (b, t) ->
        if Var.Binding.name b = name then
          subst b ~value t
        else
          Bnd (b, subst_var name ~value t)

  let op a = Opr a

  let v : string -> t = fun s -> Var (Var.v s)

  let rec subterms : t -> t list =
   fun t ->
    match t with
    | Var _       -> [ t ]
    | Bnd (_, t') -> t :: subterms t'
    | Opr o       -> t :: Op.fold (fun ts t' -> subterms t' @ ts) [] o

  let case ~var ~bnd ~opr = function
    | Var v      -> var v
    | Bnd (b, t) -> bnd (b, t)
    | Opr o      -> opr o

  let is_free_var : t -> bool =
   fun t ->
    match t with
    | Var (Free _) -> true
    | _            -> false

  let free_vars : t -> Var.Set.t =
   fun t ->
    let rec free fv = function
      | Var (Free _ as v) -> Var.Set.add v fv
      | Var (Bound _)     -> fv
      | Bnd (_, t')       -> free fv t'
      | Opr o             -> Op.fold free fv o
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

    let fail ?v t t' =
      [%log debug "unification failure: %s <> %s " (to_string t) (to_string t')];
      `Unification (v, t, t')

    let occurs_err v t =
      [%log debug "fail: %s ocurrs in %s" (Var.to_string v) (to_string t)];
      `Occurs (v, t)

    (* Error when a substitution is added for a variable already assigned to an incompatible value *)
    module Subst = struct
      type term = t

      type t =
        { bnds : Bndmap.t (* Correspondences between bindings *)
        ; vars : term ref Var.Map.t
              (* Substitution mappings from free vars to terms *)
        }
      (* Substitution maps free variables to mutable refs.
         When two free variables are assigned to be aliases, they simply share the same ref.
         Therefore, assigning one variable, sufficies to assign all of its aliases. *)

      let empty : t = { bnds = Bndmap.empty; vars = Var.Map.empty }

      (* TODO Work out coherent scheme for dealing with binder transitions! *)

      let ( let* ) = Option.bind

      (* Find is left-biased ito alpha equivalent variables *)
      let find v ({ bnds; vars } : t) =
        let* { contents = term } = Var.Map.find_opt v vars in
        match term with
        | Var (Bound bnd) ->
            Bndmap.find_left bnd bnds
            |> Option.map (fun b -> Var.of_binding b |> of_var)
        | _               -> Some term

      let bindings { vars; _ } =
        Var.Map.bindings vars |> List.map (fun (v, t) -> (v, !t))

      let term_to_string = to_string

      let to_string s =
        s
        |> bindings
        |> List.map (fun (v, term) ->
               Printf.sprintf "%s -> %s" (Var.to_string v) (to_string term))
        |> String.concat ", "
        |> Printf.sprintf "[ %s ]"

      let cycle_err s =
        [%log debug "fail: cycle between variables %s" (to_string s)];
        `Cycle s

      let add s v term =
        [%log
          debug
            "add substitution: %s -> %s"
            (Var.to_string v)
            (term_to_string term)];
        if not (Var.is_free v) then
          failwith "Invalid argument: Subst.add with non free var ";
        (* TODO Remove exponential occurs check *)
        if (not (is_free_var term)) && Var.Set.mem v (free_vars term) then
          Error (occurs_err v term)
        else
          let vars = s.vars in
          match term with
          | Bnd (_, _)
          | Opr _ -> (
              Var.Map.find_opt v vars |> function
              | None -> Ok { s with vars = Var.Map.add v (ref term) vars }
              | Some ref_term when equal !ref_term term -> Ok s
              | Some ref_var when is_free_var !ref_var ->
                  ref_var := term;
                  Ok s
              | Some clash_term -> Error (fail ~v term !clash_term))
          | Var v' ->
          match (Var.Map.find_opt v vars, Var.Map.find_opt v' vars) with
          | Some term_ref, None ->
              Ok { s with vars = Var.Map.add v' term_ref vars }
          | None, Some term_ref' ->
              Ok { s with vars = Var.Map.add v term_ref' vars }
          | Some term_ref, Some term_ref' ->
              (* TODO Should this be a structural equality check? *)
              if term_ref == term_ref' then
                Ok s
              else
                Error (fail ~v !term_ref !term_ref')
          | None, None ->
              let ref_var = ref (of_var v) in
              Ok
                { s with
                  vars = Var.Map.add v ref_var vars |> Var.Map.add v' ref_var
                }

      let log_substitution s term =
        [%log
          debug
            "applying substitution: %s %s"
            (term_to_string term)
            (to_string s)]

      (* Find the corresponding binding for substitution of a *)
      let lookup_binding lookup bnd s =
        let ( let* ) = Option.bind in
        let default = bnd |> Var.of_binding |> of_var in
        Option.value ~default
        @@ let* f = lookup in
           let* bnd' = f bnd s.bnds in
           Some (Var.of_binding bnd' |> of_var)

      exception Cycle_in_apply of t

      (* Effect the substitution of free variables in a term, according to the subtitution s
         - unassigned free var -> free var
         - assigned free var -> assigned value
         - compound term -> substitute into each of it's compounds
         - bound var -> bound var

         When [lookup] is provided, it tells us how to find binding
         correlates for the apprpriate side of a unification *)
      let apply : ?lookup:Bndmap.lookup -> t -> term -> term =
       fun ?lookup s term ->
        [%log debug "apply invoked for %s" (term_to_string term)];
        let lookup = lookup_binding lookup in
        (* cyc_vars are the vars we're already tring to substitute for
           lets us detect cycles *)
        let rec aux cyc_vars s term =
          log_substitution s term;
          match term with
          | Bnd (b, t')       -> Bnd (b, aux cyc_vars s t')
          | Opr o             -> Op.map (aux cyc_vars s) o |> op
          | Var (Bound bnd)   -> lookup bnd s
          | Var (Free _ as v) ->
          match Var.Map.find_opt v s.vars with
          | None -> term
          | Some { contents = substitute } -> (
              if Var.Set.mem v cyc_vars then raise (Cycle_in_apply s);
              let cyc_vars = Var.Set.add v cyc_vars in
              match substitute with
              | Var (Bound bnd) -> lookup bnd s
              | Var (Free _)    -> substitute
              | _               ->
                  (* TODO Shouldn't need to recurse down except to replace bindings for a side  *)
                  aux cyc_vars s substitute)
        in
        aux Var.Set.empty s term

      let ( let* ) = Result.bind

      module Op = Operator_aux (Op)

      (* Caution: Here be mutability! Never allow a mutable substitution to
         escape the abstract type! *)
      let build a b =
        [%log
          debug
            "building substitution for %s %s"
            (term_to_string a)
            (term_to_string b)];
        let rec aux s_res a b =
          let* s = s_res in
          match (a, b) with
          | Opr ao, Opr bo when Op.same ao bo -> Op.fold2 aux (Ok s) ao bo
          | Bnd (left, a'), Bnd (right, b') ->
              (* Correlate the bindings *)
              let s = { s with bnds = Bndmap.add ~left ~right s.bnds } in
              aux (Ok s) a' b'
          | Var (Free _ as v), _ -> add s v b
          | _, Var (Free _ as v) -> add s v a
          | Var (Bound _), Var (Bound _) ->
              (* We can't decide anything about bound variables at this point, assume they are ok *)
              Ok s
          | _ -> Error (fail a b)
        in
        let* subst = aux (Ok empty) a b in
        try
          Var.Map.iter (fun _ cell -> cell := apply subst !cell) subst.vars;
          [%log
            debug
              "substution for %s %s built: %s"
              (term_to_string a)
              (term_to_string b)
              (to_string subst)];
          Ok subst
        with
        | Cycle_in_apply s -> Error (cycle_err s)
    end

    let ( let* ) = Result.bind

    type error =
      [ `Unification of Var.t option * t * t
      | `Occurs of Var.t * t
      | `Cycle of Subst.t
      ]

    let unify a b =
      let result =
        [%log debug "unification start: %s =.= %s" (to_string a) (to_string b)];
        let* subst = Subst.build a b in
        let a' = Subst.apply ~lookup:Bndmap.find_left subst a in
        let b' = Subst.apply ~lookup:Bndmap.find_right subst b in
        [%log
          debug
            "checking for alpha equivalence: %s = %s"
            (to_string a')
            (to_string b')];
        if equal a' b' then
          Ok (a', subst)
        else
          Error (fail a' b')
      in
      match result with
      | Ok (u, _) ->
          [%log
            debug
              "unification success: %s =.= %s => %s"
              (to_string a)
              (to_string b)
              (to_string u)];
          result
      | Error _   ->
          [%log
            debug "unification failure: %s =/= %s" (to_string a) (to_string b)];
          result

    let ( =.= ) a b = unify a b |> Result.map fst

    let ( =?= ) a b = unify a b |> Result.is_ok
  end
end
