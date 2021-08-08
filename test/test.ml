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
      ; comp "h" [ x; y ]
      ; a
      ; b
      ; c
      ; x
      ; y
      ; z
      ]
  in
  let term = oneof [ Abt_gen.Prolog.arbitrary; terms ] in
  let open Unification in
  [ property "unification -- reflexivity" term (fun t -> t =?= t)
  ; property "unification -- transitivity" (three term) (fun (a, b, c) ->
        let a_b = a =.= b in
        let unification_of_a_and_b =
          assume (Result.is_ok a_b);
          Result.get_ok a_b
        in
        let b_c = unification_of_a_and_b =.= c in
        let unification_of_a_and_b_and_c =
          assume Result.(is_ok b_c);
          Result.get_ok b_c
        in
        a =?= unification_of_a_and_b_and_c)
  ; property "unification -- symmetry" (two term) (fun (a, b) ->
        a =?= b ==> (b =?= a))
  ]

let () = QCheck_runner.run_tests_main (utlc_tests @ unification_tests)
