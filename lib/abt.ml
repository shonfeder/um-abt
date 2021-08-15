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
      match (t, t') with
      | Opr o, Opr o'            -> Op.equal (equal bimap) o o'
      | Bnd (b, t), Bnd (b', t') ->
          (* Associate corresponding bindings in a bimap *)
          equal (Bindmap.add b b' bimap) t t'
      | Var x, Var x'            -> vars_equal bimap x x'
      | _                        -> false
    in
    fun a b -> equal Bindmap.empty a b

  let rec to_string t =
    t |> function
    | Var v        -> Var.to_string v
    | Bnd (b, abt) -> Var.(name @@ of_binding b) ^ "." ^ to_string abt
    | Opr op       -> Op.map to_string op |> Op.to_string

  let of_var : Var.t -> t = fun v -> Var v

  let rec bind : Var.Binding.t -> t -> t =
   fun bnd -> function
    | Opr op     -> Opr (Op.map (bind bnd) op)
    | Bnd (b, t) -> Bnd (b, bind bnd t)
    | Var v      ->
    match Var.bind v bnd with
    | None    -> Var v
    | Some v' -> Var v'

  let ( #. ) : string -> t -> t =
   fun name abt ->
    let binding : Var.Binding.t = Var.Binding.v name in
    let scope = bind binding abt in
    Bnd (binding, scope)

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

  let transform ~var ~bnd ~opr = function
    | Var v      -> Var (var v)
    | Opr o      -> Opr (opr o)
    | Bnd (b, t) ->
        let b, t = bnd (b, t) in
        Bnd (b, t)

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

    let fail ?v t t' : error = `Unification (v, t, t')

    let occurs_err v t : error = `Occurs (v, t)

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

      let term_to_string = to_string

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
        [%log
          debug
            "applying substitution: %s %s"
            (term_to_string term)
            (to_string s)];
        match term with
        | Bnd (b, t') -> Bnd (b, apply s t')
        | Opr o       -> Op.map (apply s) o |> op
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
        [%log
          debug
            "add substitution: %s -> %s"
            (Var.to_string v)
            (term_to_string term)];
        if (not (is_free_var term)) && Var.Set.mem v (free_vars term) then (
          [%log
            debug
              "fail: %s ocurrs in %s"
              (Var.to_string v)
              (term_to_string term)];
          Error (occurs_err v term)
        ) else if not (Var.is_free v) then
          failwith "Invalid argument: Subst.add with non free var "
        else
          match term with
          | Bnd (_, _)
          | Opr _ -> (
              Var.Map.find_opt v s |> function
              | None -> Ok (Var.Map.add v (ref term) s)
              | Some ref_term when equal !ref_term term -> Ok s
              | Some ref_var when is_free_var !ref_var ->
                  ref_var := term;
                  Ok s
              | Some clash_term -> Error (fail ~v term !clash_term))
          | Var v' ->
          match (Var.Map.find_opt v s, Var.Map.find_opt v' s) with
          | Some term_ref, None -> Ok (Var.Map.add v' term_ref s)
          | None, Some term_ref' -> Ok (Var.Map.add v term_ref' s)
          | Some term_ref, Some term_ref' ->
              if term_ref == term_ref' then
                Ok s
              else
                Error (fail ~v !term_ref !term_ref')
          | None, None ->
              let ref_var = ref (of_var v) in
              Ok (Var.Map.add v ref_var s |> Var.Map.add v' ref_var)

      let ( let* ) = Result.bind

      module Op = Operator_aux (Op)

      (* Caution: Here be mutability! Never allow a mutable substitution to escape! *)
      let build a b =
        let rec aux s_res a b =
          let* s = s_res in
          match (a, b) with
          | Opr ao, Opr bo when Op.same ao bo -> Op.fold2 aux (Ok s) ao bo
          | Bnd (_, a'), Bnd (_, b') -> aux (Ok s) a' b'
          | Var v, _ -> add s v b
          | _, Var v -> add s v a
          | _ -> Error (fail a b)
        in
        let* subst = aux (Ok empty) a b in
        Var.Map.iter (fun _ cell -> cell := apply subst !cell) subst;
        Ok (subst)
    end

    let ( let* ) = Result.bind

    let unify : t -> t -> (t * Subst.t, error) Result.t =
     fun a b ->
      let result =
        [%log debug "unification start: %s =.= %s" (to_string a) (to_string b)];
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
      | Error (`Occurs (v, t)) ->
          [%log
            debug "unification failure: %s occurs in %s" (Var.to_string v) (to_string t)];
          result
      | Error (`Unification (_, a', b')) ->
          [%log
            debug
              "unification failure: %s =.= %s => %s <> %s "
              (to_string a)
              (to_string b)
              (to_string a')
              (to_string b')];
          result

    let ( =.= ) a b = unify a b |> Result.map fst

    let ( =?= ) a b = unify a b |> Result.is_ok
  end
end
