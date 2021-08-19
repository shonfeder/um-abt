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

module type Operator = sig
  (** An operator *)

  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a

  val to_string : string t -> string
end

module Var = struct
  module Binding = struct
    type t = string ref

    let v s = ref s

    let name bnd = !bnd

    let compare a b =
      if a == b then
        0
      else
        let cmp = String.compare !a !b in
        match cmp with
        | 0 ->
            -1
            (* If different refs with the same names,
               then we just take the second ref to be bigger *)
        | _ -> cmp

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

module Bindmap : sig
  type t

  val empty : t

  val add : left:Var.Binding.t -> right:Var.Binding.t -> t -> t

  type lookup = Var.Binding.t -> t -> Var.Binding.t option

  (* [find bnd m] is the binding corresponding to [bnd], regardless of which
     side it was entered from *)
  val find : lookup


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
  let find k m =
    match M.find_opt k m.left with
    | None   -> M.find_opt k m.right
    | Some v -> Some v

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

module Make (Op : Operator) = struct
  type t =
    | Var of Var.t
    | Bnd of Var.Binding.t * t
    | Opr of t Op.t

  (* Alpha-equivalence is derived by checking that the structure of the
     two abts is the same.

     - For operators, this just amounts to checking the equality supplied by the
       given {!modtype:Operator}, [O].
     - For variable, we check that the pointer {i structure} is equivalent, and
       do take no account of names, since alpha equivalence is fundamentally
       concerned with the (anonymous) binding structure of ABTs. *)
  let equal : t -> t -> bool =
    let vars_equal bimap x x' =
      match Var.(to_binding x, to_binding x') with
      | Some _, None    -> false
      | None, Some _    -> false
      | None, None      -> Var.equal x x'
      | Some b, Some b' ->
      (* Two bound variables are equal when their bindings correspond *)
      match Bindmap.find b bimap with
      | Some b'' -> Var.Binding.equal b' b''
      | None     -> false
    in
    let rec equal : Bindmap.t -> t -> t -> bool =
     fun bimap t t' ->
      match (t, t') with
      | Opr o, Opr o' -> Op.equal (equal bimap) o o'
      | Bnd (left, t), Bnd (right, t') ->
          (* Associate corresponding bindings in a bimap *)
          equal (Bindmap.add ~left ~right bimap) t t'
      | Var x, Var x' -> vars_equal bimap x x'
      | _ -> false
    in
    fun a b -> equal Bindmap.empty a b

  let rec to_string t =
    t |> function
    | Var v        -> Var.to_string v
    | Bnd (b, abt) -> Var.(name @@ of_binding b) ^ "." ^ to_string abt
    | Opr op       -> Op.map to_string op |> Op.to_string

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
    module Log = Logs

    (* Initial, naive approach:
     *   1. get all free vars of a and b
     *   1. build mgu and substitute for all vars
     *   3. then check for alpha-equiv
     *
     * Will take 3n complexity
     *
     * TODO To optimize: need to unify on a single pass, which will require way of identifying if two
     * operators have the same head. Perhaps via an operator function `sort : O.t -> (string * int)`? *)

    type error =
      [ `Unification of Var.t option * t * t
      | `Occurs of Var.t * t
      ]

    let fail ?v t t' : error =
      [%log debug "unification failure: %s <> %s " (to_string t) (to_string t')];
      `Unification (v, t, t')

    let occurs_err v t : error =
      [%log debug "fail: %s ocurrs in %s" (Var.to_string v) (to_string t)];
      `Occurs (v, t)

    (* Error when a substitution is added for a variable already assigned to an incompatible value *)
    module Subst = struct
      type term = t

      type t =
        { bnds : Bindmap.t (* Correspondences between bindings *)
        ; vars : term ref Var.Map.t
              (* Substitution mappings from free vars to terms *)
        }
      (* Substitution maps free variables to mutable refs.
         When two free variables are assigned to be aliases, they simply share the same ref.
         Therefore, assigning one variable, sufficies to assign all of its aliases. *)

      let empty : t = { bnds = Bindmap.empty; vars = Var.Map.empty }

      (* TODO Work out coherent scheme for dealing with binder transitions! *)

      let ( let* ) = Option.bind

      (* Find is left-biased ito alpha equivalent variables *)
      let find v ({ bnds; vars } : t) =
        let* { contents = term } = Var.Map.find_opt v vars in
        match term with
        | Var (Bound bnd) ->
            Bindmap.find_left bnd bnds
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

      (* TODO Remove exponential occurs check *)
      let add : t -> Var.t -> term -> (t, error) Result.t =
       fun s v term ->
        [%log
          debug
            "add substitution: %s -> %s"
            (Var.to_string v)
            (term_to_string term)];
        if not (Var.is_free v) then
          failwith "Invalid argument: Subst.add with non free var ";
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

      (* TODO Use in application *)
      let _ = Bindmap.find_right

      (* Effect the substitution of free variables in a term, according to the subtitution s
         - unassigned free var -> free var
         - assigned free var -> assigned value
         - compound term -> substitute into each of it's compounds
         - bound var -> bound var

         When [lookup] is provided, it tells us how to find binding
         correlates for the proper side of a unification *)
      let apply : ?lookup:Bindmap.lookup -> t -> term -> term =
       fun ?lookup s term ->
       let _ = lookup in
       let rec aux s term =
        [%log
          debug
            "applying substitution: %s %s"
            (term_to_string term)
            (to_string s)];
        match term with
        | Bnd (b, t')        -> Bnd (b, aux s t')
        | Opr o              -> Op.map (aux s) o |> op
        | Var (Bound _ as v) -> of_var v
        | Var (Free _ as v)  ->
            Var.Map.find_opt v s.vars
            |> Option.map (fun { contents } ->
                   if not (is_free_var contents) then
                     aux s contents
                   else
                     contents)
            |> Option.value ~default:term
       in
       aux s term

      let ( let* ) = Result.bind

      module Op = Operator_aux (Op)

      (* Caution: Here be mutability! Never allow a mutable substitution to
         escape the abstract type! *)
      let build a b =
        let rec aux s_res a b =
          let* s = s_res in
          match (a, b) with
          | Opr ao, Opr bo when Op.same ao bo -> Op.fold2 aux (Ok s) ao bo
          | Bnd (left, a'), Bnd (right, b') ->
              (* Correlate the bindings *)
              let s = { s with bnds = Bindmap.add ~left ~right s.bnds } in
              aux (Ok s) a' b'
          | Var (Free _ as v), _ -> add s v b
          | _, Var (Free _ as v) -> add s v a
          | Var (Bound _), Var (Bound _) ->
              (* We can't decide anything about bound variables at this point, assume they are ok *)
              Ok s
          | _ -> Error (fail a b)
        in
        let* subst = aux (Ok empty) a b in
        Var.Map.iter (fun _ cell -> cell := apply subst !cell) subst.vars;
        Ok subst
    end

    let ( let* ) = Result.bind

    let unify : t -> t -> (t * Subst.t, error) Result.t =
     fun a b ->
      let result =
        [%log debug "unification start: %s =.= %s" (to_string a) (to_string b)];
        (* TODO Build bmap *)
        let* subst = Subst.build a b in
        let a' = Subst.apply subst a in
        let b' = Subst.apply subst b in
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
