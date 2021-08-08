module Var = struct
  let var_name_gen =
    let open QCheck.Gen in
    map (String.make 1) (char_range 'a' 'z')

  let var_name_gen_caps =
    let open QCheck.Gen in
    map (String.make 1) (char_range 'A' 'Z')

  let binding_gen =
    let open QCheck.Gen in
    map Abt.Var.Binding.v var_name_gen

  let var_gen =
    let open QCheck.Gen in
    oneof [ map Abt.Var.v var_name_gen; map Abt.Var.of_binding binding_gen ]

  let arbitrary = QCheck.make ~print:Abt.Var.to_string var_gen
end

module Utlc = struct
  open Example.Untyped_lambda_calculus.Syntax

  let gen =
    let open QCheck.Gen in
    sized
    @@ fix (fun self -> function
         | 0 -> map v Var.var_name_gen
         | n ->
             frequency
               [ (1, map2 app (self (n / 2)) (self (n / 2)))
               ; (1, map2 lam Var.var_name_gen (self (n / 2)))
               ])

  let rec shrink t =
    let open QCheck.Iter in
    t
    |> case
         ~var:(Fun.const empty)
         ~bnd:(fun (bnd, t) -> return t <+> shrink t >|= bind bnd)
         ~opr:(function
           | Lam t      -> shrink t
           | App (m, n) ->
               of_list [ m; n ]
               <+> (shrink m >|= fun m' -> app m' n)
               <+> (shrink n >|= fun n' -> app m n'))

  let arbitrary = QCheck.make ~print:to_string gen ~shrink
end

module Prolog = struct
  open Example.Prolog.Syntax

  let gen =
    let open QCheck.Gen in
    sized
    @@ fix (fun self size ->
           match size with
           | 0 ->
               frequency
                 [ (1, map atom Var.var_name_gen)
                 ; (1, map v Var.var_name_gen_caps)
                 ]
           | n -> map2 comp Var.var_name_gen (list_size (0 -- 5) (self (n / 10))))

  let rec shrink t =
    let open QCheck.Iter in
    t
    |> case
         ~var:(Fun.const empty)
         ~bnd:(fun (bnd, t) -> return t <+> shrink t >|= bind bnd)
         ~opr:(fun o ->
           match o with
           | Atom _             -> empty
           | Compound (_, args) -> of_list args)

  let arbitrary = QCheck.make ~print:to_string ~shrink gen
end
