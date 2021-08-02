open QCheck

let count = 1000

let property name = Test.make ~count ~name

let utlc_tests =
  let open Example.Untyped_lambda_calculus.Syntax in
  let ( = ) = equal in
  let term = Abt_gen.Utlc.arbitrary in
  [ property "alpha equivalence -- reflexivity" term (fun t -> t = t)
  ; property
      "alpha equivalance -- compatibility"
      (triple term term term)
      (fun (l, m, n) -> m = n ==> (app m l = app n l && app l m = app l n))
  ; property "alpha equivalence -- symmetry" (pair term term) (fun (m, n) ->
        m = n ==> (n = m))
  ; property
      "alpha equivalence -- transitivity"
      (triple term term term)
      (fun (l, m, n) -> (l = m && m = n) ==> (l = n))
  ]

let () = QCheck_runner.run_tests_main utlc_tests
