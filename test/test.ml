open QCheck

let count = 1000

let property name = Test.make ~count ~name

let three x = triple x x x

let two x = pair x x

let utlc_tests =
  let open Example.Untyped_lambda_calculus.Syntax in
  let ( = ) = equal in
  let x, y, z = (v "x", v "y", v "z") in
  let s = oneofl [ lam "x" (lam "y" (lam "z" (app (app x y) (app y z)))) ] in
  let k = oneofl [ lam "x" (lam "y" x); lam "y" (lam "x" y) ] in
  let i = oneofl [ lam "x" x; lam "y" y; lam "z" z ] in
  let ski = oneof [ s; k; i ] in
  let term = Abt_gen.Utlc.arbitrary in
  [ property "alpha equivalence -- reflexivity" term (fun t -> t = t)
  ; property
      "alpha equivalance -- compatibility"
      (oneof [ three term; three ski ])
      (fun (l, m, n) -> m = n ==> (app m l = app n l && app l m = app l n))
  ; property
      "alpha equivalence -- symmetry"
      (oneof [ two term; two ski ])
      (fun (m, n) -> m = n ==> (n = m))
  ; property
      "alpha equivalence -- transitivity"
      (oneof [ three term; three ski ])
      (fun (l, m, n) -> (l = m && m = n) ==> (l = n))
  ]

let unification_tests =
  (* Logs.set_level (Some Logs.Debug); *)
  let open Example.Prolog.Syntax in
  (* let ( = ) = equal in *)
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
  let term = oneof [ Abt_gen.Prolog.arbitrary; terms ] in
  let assume_unified result =
    assume (Result.is_ok result);
    Result.get_ok result
  in
  let open Unification in
  [ property "unification -- reflexivity" term (fun t -> t =?= t)
  ; property "unification -- transitivity" (three term) (fun (a, b, c) ->
        let a_b = a =.= b |> assume_unified in
        let b_c = a_b =.= c |> assume_unified in
        a =?= b_c)
  ; property "unification -- symmetry" (two term) (fun (a, b) ->
        a =?= b ==> (b =?= a))
  ; property
      "unification -- with free variable"
      (pair Abt_gen.Var.arbitrary_free term)
      (fun (v, t) ->
        match of_var v =.= t with
        (* Either the unification succeeds *)
        | Ok t' -> (
            match t with
            (* and if the rhs term was also a free var, than the unified term is equal to lhs variable *)
            | Var (Free _) -> equal t' (of_var v)
            (* or the unified term is equal to the rhs term *)
            | _ -> equal t t')
        (* or the unification failes, due to the occurs check *)
        | Error (`Occurs (v', t')) ->
            (* In which case the error must return the free lhs free variable and the rhs term *)
            Abt.Var.equal v v' && equal t t'
        | _ -> false)
  ]

let () = QCheck_runner.run_tests_main (utlc_tests @ unification_tests)
