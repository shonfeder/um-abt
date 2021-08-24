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

open! Bos_setup

module Untyped_lambda_calculus = struct
  module Syntax = struct
    (** Syntax for the simply typed lambda calculus *)

    module O = struct
      type 'a t =
        | App of 'a * 'a
        | Lam of 'a
      [@@deriving eq, map, fold]

      let to_string : string t -> string = function
        | App (l, m) -> Printf.sprintf "(%s %s)" l m
        | Lam abs    -> Printf.sprintf "(λ%s)" abs
    end

    include Abt.Make (O)

    let app m n = op (App (m, n))

    let lam x m = op (Lam x#.m)

    let show s = to_string s |> print_endline
  end

  (* Evaluation for the simply typed lambda calculus *)

  open Syntax

  let rec eval : t -> t =
   fun t ->
    match t with
    | Opr (App (m, n)) -> apply (eval m) (eval n)
    (* No other terms can be evaluated *)
    | _ -> t

  and apply : t -> t -> t =
   fun m n ->
    match m with
    | Bnd (bnd, t) -> subst bnd ~value:n t
    | Opr (Lam bnd) -> eval (apply bnd n)
    (* otherwise the application can't be evaluated *)
    | _ -> app m n

  module Examples = struct
    open Syntax

    let x, y, z, m, n = (v "x", v "y", v "z", v "m", v "n")

    let%expect_test "Utlc terms" =
      show (app (lam "m" m) (lam "x" x));
      [%expect {| ((λm.m) (λx.x)) |}];

      show (app m n);
      [%expect {| (m n) |}]

    let%expect_test "Utlc evaluation" =
      show @@ eval (app (lam "x" x) m);
      [%expect {| m |}];

      show @@ eval (app (lam "z" (app (lam "x" x) z)) m);
      [%expect {| m |}];

      let a = app (app (lam "z" z) (lam "z" z)) m in
      show a;
      [%expect {| (((λz.z) (λz.z)) m) |}];
      show @@ eval a;
      [%expect {| m |}];

      show
      @@ eval (app (lam "z" (app (lam "x" x) z)) (app (lam "y" y) (lam "z" n)));
      [%expect {| (λz.n) |}]

    let%expect_test "unification of Utlc" =
      let open Syntax in
      let exp1 = app (v "M") (app (lam "x" (lam "y" y)) z) in
      let exp2 = app (lam "x" x) (v "N") in

      show exp1;
      [%expect {| (M ((λx.(λy.y)) z)) |}];
      show exp2;
      [%expect {| ((λx.x) N) |}];

      let open Unification in
      let unified_term, substitution = unify exp1 exp2 |> Result.get_ok in

      show unified_term;
      [%expect {| ((λx.x) ((λx.(λy.y)) z)) |}];

      Subst.to_string substitution |> print_endline;
      [%expect {| [ M -> (λx.x), N -> ((λx.(λy.y)) z) ] |}];

      (* Alpha equivalent terms unify *)
      let s = lam "x" (lam "y" x) in
      let s' = lam "y" (lam "x" y) in

      equal s s' |> Bool.to_string |> print_endline;
      [%expect {|true|}];

      s =?= s' |> Bool.to_string |> print_endline;
      [%expect {|true|}];

      let k_combinator = lam "x" (lam "y" x) in
      let z_M = lam "z" (v "M") in

      show k_combinator;
      [%expect {|(λx.(λy.x))|}];
      show z_M;
      [%expect {|(λz.M)|}];

      (* Unification is "nominal" (i.e., modulo ɑ-equivalence) *)
      show (z_M =.= k_combinator |> Result.get_ok);
      [%expect {|(λz.(λy.z))|}];

      (* These two terms turned up a problem in the ɑ-equivalence alogrithm *)
      let lhs =
        lam
          "a"
          (lam
             "e"
             (app
                (lam "f" (lam "r" (lam "q" (app (v "u") (v "x")))))
                (lam
                   "s"
                   (app
                      (app (lam "i" (v "m")) (lam "t" (v "y")))
                      (app (app (v "c") (v "j")) (lam "f" (v "a")))))))
      in
      let rhs = lam "n" (lam "b" (app (lam "c" (v "l")) (lam "n" (v "v")))) in
      show lhs;
      [%expect
        {|(λa.(λe.((λf.(λr.(λq.(u x)))) (λs.(((λi.m) (λt.y)) ((c j) (λf.a)))))))|}];
      show rhs;
      [%expect {|(λn.(λb.((λc.l) (λn.v))))|}];

      show (lhs =.= rhs |> Result.get_ok);
      [%expect
        {|(λa.(λe.((λf.(λr.(λq.(u x)))) (λs.(((λi.m) (λt.y)) ((c j) (λf.a)))))))|}];

      show (rhs =.= lhs |> Result.get_ok);
      [%expect
        {|(λn.(λb.((λc.(λr.(λq.(u x)))) (λn.(((λi.m) (λt.y)) ((c j) (λf.n)))))))|}];

      assert (equal (rhs =.= lhs |> Result.get_ok) (lhs =.= rhs |> Result.get_ok))
  end
end

module Arithmetic_expressions = struct
  module Syntax = struct
    module O = struct
      type 'a t =
        | Num of int
        | Plus of 'a * 'a
      [@@deriving fold]

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

    include Abt.Make (O)

    let num n = op (Num n)

    let plus a b = op (Plus (a, b))

    let show t = to_string t |> print_endline
  end

  module Semantics = struct
    open Syntax

    let ( let* ) = Option.bind

    let rec reduce : t -> int option = function
      | Var _ -> None
      | Bnd _ -> None
      | Opr o ->
      match o with
      | Num n       -> Some n
      | Plus (a, b) ->
          let* a = reduce a in
          let* b = reduce b in
          Some (a + b)

    let rec eval : t -> t = function
      | Var _ as v -> v
      | Bnd (b, t) -> bind b (eval t)
      | Opr o      ->
      match o with
      | Num n       -> num n
      | Plus (a, b) ->
      match (reduce a, reduce b) with
      | None, None      -> plus a b
      | Some n, Some n' -> num (n + n')
      | Some n, None    -> plus (num n) b
      | None, Some n'   -> plus a (num n')
  end

  let x, y, z = Syntax.(v "x", v "y", v "z")

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

  let%expect_test "unification of expression language" =
    let open Syntax in
    let exp1 = plus x one in
    let exp2 = plus (plus y two) y in

    show exp1;
    [%expect {| (x + 1) |}];

    show exp2;
    [%expect {| ((y + 2) + y) |}];

    let open Unification in
    let unified_term, substitution = unify exp1 exp2 |> Result.get_ok in

    show unified_term;
    [%expect {| ((1 + 2) + 1) |}];

    Subst.to_string substitution |> print_endline;
    [%expect {| [ x -> (1 + 2), y -> 1 ] |}]
end

module Prolog = struct
  module Syntax = struct
    module O = struct
      type 'a t =
        | Atom of string
        | Compound of string * 'a list
      [@@deriving eq, map, fold]

      let to_string : string t -> string = function
        | Atom a             -> a
        | Compound (f, args) ->
            Printf.sprintf "%s(%s)" f (String.concat ~sep:", " args)
    end

    include Abt.Make (O)

    let atom a = op (Atom a)

    let comp f args = op (Compound (f, args))

    let show t = to_string t |> print_endline
  end

  module Example = struct
    open Syntax

    let x, y = (v "X", v "Y")

    let a, b = (atom "a", atom "b")

    let%expect_test "Prolog terms" =
      show (atom "a");
      [%expect {| a |}];

      show (comp "f" [ a; x ]);
      [%expect {| f(a, X) |}];

      show (comp "f" [ y; comp "g" [ a; b ] ]);
      [%expect {| f(Y, g(a, b)) |}];

      (* We don't hit Norvig's unification bug https://norvig.com/unify-bug.pdf *)
      show
        Unification.(comp "f" [ x; y ] =.= comp "f" [ y; x ] |> Result.get_ok);
      [%expect {| f(X, X) |}]
  end
end
