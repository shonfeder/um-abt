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

open QCheck

let count = 1000

let property name = Test.make ~count ~name

let three x = triple x x x

let two x = pair x x

module type Syntax_tester = sig
  val name : string

  module Syntax : Abt.Syntax

  val term : Syntax.t arbitrary
end

(* Generates unification property tests for a the given syntax *)
module Unification_properties (Tester : Syntax_tester) = struct
  open Tester.Syntax
  open Unification

  let term = Tester.term

  let assume_unified result =
    assume (Result.is_ok result);
    Result.get_ok result

  let property name = property (Tester.name ^ " -- unification:" ^ name)

  let properties =
    [ property "reflexivity" term (fun t -> t =?= t)
    ; property "symmetry" (two term) (fun (a, b) -> a =?= b ==> (b =?= a))
    ; (* TODO Fix transitivity when occurs check fails. Use seed 399269583  *)
      property "transitivity" (three term) (fun (a, b, c) ->
          let a_b = a =.= b |> assume_unified in
          let b_c = a_b =.= c |> assume_unified in
          a =?= b_c)
    ; property
        "free variables unify (unless occurs check fails)"
        (pair Abt_gen.Var.arbitrary_free term)
        (fun (v, t) ->
          match of_var v =.= t with
          (* If the unification succeeds *)
          | Ok t' -> (
              match t with
              (* and the rhs term was also a free var, then the unified term is equal to the lhs variable. *)
              | Var (Free _) -> equal t' (of_var v)
              (* Otherwise, the unified term is equal to the rhs term. *)
              | _ -> equal t t')
          (*  If the unification failes due to the occurs check *)
          | Error (`Occurs (v', t')) ->
              (* then the error must return the free lhs free variable and the rhs term *)
              Abt.Var.equal v v' && equal t t'
          (* Any other failure is an incorrect *)
          | _ -> false)
    ; property "equal terms unify" (two term) (fun (a, b) ->
          (not (equal a b)) || a =?= b)
      (* TODO The following is invalid for nominal unificaiton due to difference in binding names
              find the property that actually does hold. *)
      (* ; property
       *     "all free vars in terms are bound to subterms in unification"
       *     (two term)
       *     (fun (a, b) ->
       *       let u, substitution = unify a b |> assume_unified in
       *       let u_free_vars = free_vars u in
       *       let u_subterms = subterms u in
       *
       *       let bound_a_vars = Abt.Var.Set.diff (free_vars a) u_free_vars in
       *       let all_bound_free_vars_in_a_are_bound_to_subterms_of_unified =
       *         bound_a_vars
       *         |> Abt.Var.Set.for_all (fun v ->
       *                List.mem (Subst.find v substitution |> Option.get) u_subterms)
       *       in
       *
       *       let bound_b_vars = Abt.Var.Set.diff (free_vars b) u_free_vars in
       *       let all_bound_free_vars_in_b_are_bound_to_subterms_of_unified =
       *         bound_b_vars
       *         |> Abt.Var.Set.for_all (fun v ->
       *                List.mem (Subst.find v substitution |> Option.get) u_subterms)
       *       in
       *
       *       all_bound_free_vars_in_a_are_bound_to_subterms_of_unified
       *       && all_bound_free_vars_in_b_are_bound_to_subterms_of_unified) *)
    ]
end

let arbitrary_utlc_term =
  let open Example.Untyped_lambda_calculus.Syntax in
  let x, y, z = (v "x", v "y", v "z") in
  let s = oneofl [ lam "x" (lam "y" (lam "z" (app (app x y) (app y z)))) ] in
  let k = oneofl [ lam "x" (lam "y" x); lam "y" (lam "x" y) ] in
  let i = oneofl [ lam "x" x; lam "y" y; lam "z" z ] in
  oneof [ Abt_gen.Utlc.arbitrary; s; k; i ]

let utlc_tests =
  let term = arbitrary_utlc_term in
  let open Example.Untyped_lambda_calculus.Syntax in
  [ property "alpha equivalence -- reflexivity" term (fun t -> t = t)
  ; property
      "utlc -- alpha equivalance -- compatibility"
      (three term)
      (fun (l, m, n) -> m = n ==> (app m l = app n l && app l m = app l n))
  ; property
      "utlc -- alpha equivalence -- symmetry"
      (oneof
         [ two term
         ; pair
             (always @@ lam "x" (lam "y" (v "x")))
             (always @@ lam "r" (lam "r" (v "r")))
         ])
      (fun (m, n) -> m = n ==> (n = m))
  ; property
      "utlc -- alpha equivalence -- transitivity"
      (three term)
      (fun (l, m, n) -> (l = m && m = n) ==> (l = n))
  ; property "utlc -- unifiction -- reflexivity" term (fun m ->
        Unification.(m =?= m))
  ]

let arbitrary_prolog_term =
  let open Example.Prolog.Syntax in
  let x, y, z = (v "X", v "Y", v "Z") in
  let a, b, c = (atom "a", atom "b", atom "c") in
  let terms =
    oneofl
      [ comp "f" [ x; a ]
      ; comp "g" [ b; y; a ]
      ; comp "h" [ x; comp "i" [ y; a; z ] ]
      ; a
      ; b
      ; c
      ; x
      ; y
      ; z
      ]
  in
  oneof [ Abt_gen.Prolog.arbitrary; terms ]

module Utlc_unification_properties = Unification_properties (struct
  let name = "utlc"

  module Syntax = Example.Untyped_lambda_calculus.Syntax

  let term = arbitrary_utlc_term
end)

module Prolog_unification_properties = Unification_properties (struct
  let name = "prolog"

  module Syntax = Example.Prolog.Syntax

  let term = arbitrary_prolog_term
end)

let () =
  (* Logs.set_level (Some Logs.Debug); *)
  QCheck_runner.run_tests_main
    (utlc_tests
    @ Utlc_unification_properties.properties
    @ Prolog_unification_properties.properties)
