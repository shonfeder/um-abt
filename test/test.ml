open QCheck

let count = 1000

let property name = Test.make ~count ~name

let utlc_tests =
  let open Example.Untyped_lambda_calculus.Syntax in
  let ( = ) = equal in
  let x, y, z = (v "x", v "y", v "z") in
  let s = oneofl [ lam "x" (lam "y" (lam "z" (app (app x y) (app y z)))) ] in
  let k = oneofl [ lam "x" (lam "y" x); lam "y" (lam "x" y) ] in
  let i = oneofl [ lam "x" x; lam "y" y; lam "z" z ] in
  let ski = oneof [ s; k; i ] in
  let three x = triple x x x in
  let two x = pair x x in
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

(* let unification_tests =
 *   let open Example.Arithmetic_expressions.Syntax in
 *   let ( = ) = equal in
 *   let x, y, z = (v "X", v "Y", v "Z") in
 *   let  *)

let () = QCheck_runner.run_tests_main utlc_tests
