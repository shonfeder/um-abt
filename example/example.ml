module Untyped_lambda_calculus = struct
  module Syntax = struct
    (** Syntax for the simply typed lambda calculus *)

    module Op = struct
      type 'a t =
        | App of 'a * 'a
        | Lam of 'a
      [@@deriving eq, map, show]

      let to_string : string t -> string = function
        | App (l, m) -> Printf.sprintf "(%s %s)" l m
        | Lam abs    -> Printf.sprintf "(λ%s)" abs
    end

    include Abt.Make (Op)

    type op = t Op.t

    let app m n = op (App (m, n))

    let lam x m = op (Lam x#.m)

    let show s = to_string s |> print_endline
  end

  module Semantics = struct
    (** Semantics for the simply typed lambda calculus *)

    open Syntax

    let rec eval : t -> t =
     fun t ->
      let var = Fun.const t in
      let bnd = Fun.const t in
      let opr = function
        | Op.App (m, n) -> apply (eval m) (eval n)
        | Op.Lam abs    -> op (Op.Lam abs)
      in
      case ~var ~bnd ~opr t

    and apply : t -> t -> t =
     fun m n ->
      let var _ = app m n in
      let bnd (b, t) = subst b ~value:n t in
      let opr = function
        | Op.App (_, _) -> app m n
        | Op.Lam bnd    -> eval (apply bnd n)
      in
      case ~var ~opr ~bnd m
  end

  module Examples = struct
    open Syntax

    let x, y, z, m, n = (v "x", v "y", v "z", v "m", v "n")

    let%expect_test "Utlc terms" =
      show (app (lam "m" m) (lam "x" x));
      [%expect {| ((λm.m) (λx.x)) |}];

      show (app m n);
      [%expect {| (m n) |}]

    let%expect_test "Utlc evaluation" =
      show @@ Semantics.eval (app (lam "x" x) m);
      [%expect {| m |}];

      show @@ Semantics.eval (app (lam "z" (app (lam "x" x) z)) m);
      [%expect {| m |}];

      show
      @@ Semantics.eval
           (app (lam "z" (app (lam "x" x) z)) (app (lam "y" y) (lam "z" n)));
      [%expect {| (λz.n) |}]
  end
end

module Arithmetic_expressions = struct
  module Syntax = struct
    module Op = struct
      type 'a t =
        | Num of int
        | Plus of 'a * 'a

      let equal eq a b =
        match (a, b) with
        | Num n, Num n'              -> Int.equal n n'
        | Plus (a, b), Plus (a', b') -> eq a a' && eq b b'
        | _                          -> false

      let map f t =
        match t with
        | Num n       -> Num n
        | Plus (a, b) -> Plus (f a, f b)

      let to_string : string t -> string = function
        | Num n       -> Int.to_string n
        | Plus (a, b) -> Printf.sprintf "(%s + %s)" a b
    end

    include Abt.Make (Op)

    let num n = op (Num n)

    let plus a b = op (Plus (a, b))

    let show t = to_string t |> print_endline
  end

  module Semantics = struct
    open Syntax

    let rec reduce : t -> int option =
     fun t ->
      let var = Fun.const None in
      let bnd = Fun.const None in
      let opr =
        let open Op in
        function
        | Num n       -> Some n
        | Plus (a, b) ->
        match (reduce a, reduce b) with
        | None, _
        | _, None ->
            None
        | Some a, Some b -> Some (a + b)
      in
      case t ~var ~bnd ~opr

    let rec eval : t -> t =
     fun t ->
      let var = Fun.id in
      let bnd (b, t) = (b, eval t) in
      let opr =
        let open Op in
        function
        | Num n       -> Num n
        | Plus (a, b) ->
        match (reduce a, reduce b) with
        | None, None      -> Plus (a, b)
        | Some n, Some n' -> Num (n + n')
        | Some n, None    -> Plus (num n, b)
        | None, Some n'   -> Plus (a, num n')
      in
      transform t ~var ~bnd ~opr
  end

  let one = Syntax.(num 1)

  let two = Syntax.(num 2)

  let%expect_test "scalars" =
    Syntax.show one;
    [%expect {| 1 |}];

    Syntax.show two;
    [%expect {| 2 |}]

  let one_plus_x = Syntax.(plus one (v "x"))

  let one_plus_y = Syntax.(plus one (v "y"))

  let%expect_test "free variables" =
    Syntax.show one_plus_x;
    [%expect {| (1 + x) |}];
    Syntax.show one_plus_y;
    [%expect {| (1 + y) |}];
    (* Free variables are not alpha equivalent  *)
    assert (Syntax.(not @@ equal one_plus_x one_plus_y))

  let shadow_x_in_bound_x = Syntax.("x" #. (plus "x"#.one_plus_x (v "x")))

  let bind_x_in_bound_y = Syntax.("y" #. (plus "x"#.one_plus_x (v "y")))

  let%expect_test "shadowing and binding" =
    Syntax.show shadow_x_in_bound_x;
    [%expect {| x.(x.(1 + x) + x) |}];

    Syntax.show bind_x_in_bound_y;
    [%expect {| y.(x.(1 + x) + y) |}];

    (* Bound variables allow alpha equivalence *)
    assert (Syntax.(equal shadow_x_in_bound_x bind_x_in_bound_y))

  let subst1 = Syntax.(shadow_x_in_bound_x |> subst_var "x" ~value:(num 3))

  let fully_bound = Syntax.(subst1 |> subst_var "x" ~value:(num 99))

  let%expect_test "substitution" =
    (* Substitution respects shadowed scope *)
    Syntax.show subst1;
    [%expect {| (x.(1 + x) + 3) |}];

    (* Subsequent substitution works as expected *)
    Syntax.(subst1 |> subst_var "x" ~value:(num 4) |> show);
    [%expect {| ((1 + 4) + 3) |}];

    (* Substitution does not mutate abts, so we can give alternate assignments to
       previously defined trees. *)
    Syntax.show fully_bound;
    [%expect {| ((1 + 99) + 3) |}];

    Semantics.eval fully_bound |> Syntax.show;
    [%expect {| 103 |}];

    Semantics.eval Syntax.(subst_var "x" ~value:(num 4) bind_x_in_bound_y)
    |> Syntax.show;
    [%expect {| y.(5 + y) |}]
end