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

  let x, y, z, m, n = v "x", v "y", v "z", v "m", v "n"

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

    show @@ Semantics.eval (app (lam "z" (app (lam "x" x) z)) (app (lam "y" y) (lam "z" n)));
    [%expect {| (λz.n) |}]
end
