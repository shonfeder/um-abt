# um-abt

An OCaml library implementing abstract binding trees (ABTs) exhibiting with the
properties defined in [Robert Harper](https://www.cs.cmu.edu/~rwh/pfpl/)'s
[Practical Foundations for Programming Labguages](https://www.cs.cmu.edu/~rwh/pfpl/)
(PFPL).

## Features

This ABT library has two distinctive (afaik) features:

1. It implements variable binding via *binding by reference*; i.e., variable
   binding is implemented by way of "immutable" reference cells. I believe the
   advantages of this approach to include:

   - a trivial algorithm for computing ɑ-equivalence
   - neutralization of the usual problem of renaming bound variables
   - the representation is easy to read, in contrast with De Bruijn indices,
     and, even more important, there's no tedious book keeping required during
     substitution.
   - the representation is trivial to inspect and manipulate, in contrast with
     [HOAS][]

   However, I suspect this approach lacks the safety and formal elegance of HOAS
   or [NbE](https://en.wikipedia.org/wiki/Normalisation_by_evaluation). The
   approach used here is also dependent on OCaml's definition of physical
   equality for `ref` cells, and on MLs ability to ensure that the references
   are immutable via type abstraction.

2. The library augments the binding functionality of the ABT approach with
   general syntactic (perhaps later also equational) unification. We might
   therefore describe this library as an implentation of *unifiable* abstract
   binding trees (or UABTs). ABTs provide a generalized a reusable system for
   variable binding for any language implemented in its terms. UABTs provide --
   in addition -- a generalized, reusable system for (first-order, syntactic)
   unification for any language implented in its terms.

[HOAS]: https://en.wikipedia.org/wiki/Higher-order_abstract_syntax

## Examples

Here is a short example showing a naive implementation of the simply typed
lambda calculus using um-abt:

```ocaml
module Syntax = struct
  (** Syntax for the simply typed lambda calculus *)

  (* Define the operators for your language *)
  module Op = struct
      type 'a t =
      | App of 'a * 'a
      | Lam of 'a
      [@@deriving eq, map, fold]

      let to_string : string t -> string = function
      | App (l, m) -> Printf.sprintf "(%s %s)" l m
      | Lam abs    -> Printf.sprintf "(λ%s)" abs
  end

  (* Generate the syntax, which will include a type [t] of the ABTs over the operators **)
  include Abt.Make (Op)

  (* Define some convenient constructors *)

  let app m n : t = 
    (* [op] makes an operator into an ABT *)
    op (App (m, n))

  let lam x m : t = 
    (* ["x" #. scope] binds all free variables named "x" in the [scope] *)
    op (Lam (x #. m))
end

module Semantics = struct
  (** Semantics for the simply typed lambda calculus *)

  open Syntax

  let rec eval : t -> t =
   fun t -> 
     (* The [case] function lets us deconstruct the ABT by case analysis,
        whithout having to compromise on the guarantees we gain by keeping 
        its type abstract. *)
     t |> case 
        ~var:(Fun.const t) (* variables are left uninterpreted *)
        ~bnd:(Fun.const t) (* bindings are left uninterpreted *)
        ~opr:(function
              | Op.App (m, n) -> apply (eval m) (eval n)
              | Op.Lam abs    -> op (Op.Lam abs))

  and apply : t -> t -> t =
   fun m n ->
    let var _ = app m n in
    (* [subst b ~value t] is t[x := value] for all variables [x] bound to [b] *)
    let bnd (b, t) = subst b ~value:n t in
    let opr = function
      | Op.App (_, _) -> app m n
      | Op.Lam bnd    -> eval (apply bnd n)
    in
    case ~var ~opr ~bnd m
end

(* [v x] is a free variable named "x" *)
let x, y, z = Syntax.(v "x", v "y", v "z")

(* We define the SKI combinators *)
let s = Syntax.(lam "x" (lam "y" (lam "z" (app (app x y) (app y z)))))
let k = Syntax.(lam "x" (lam "y" x))
let i = Syntax.(lam "x" x)

let () =
  (* Equality between ABTs is defined in terms of ɑ-equivalence *)
  assert Syntax.(equal i (lam "y" y))

let () = 
  (* Here's what the combinators look like as strings *)
  assert (Syntax.to_string s = "(λx.(λy.(λz.((x y) (y z)))))");
  assert (Syntax.to_string k = "(λx.(λy.x))");
  assert (Syntax.to_string i = "(λx.x)")
  

let () =
  (* Let's fix our equality to be in terms of ɑ-equivalent ABTs *)
  let (=) = Syntax.equal in
  (* So we can test some evaluations 
     (See https://en.wikipedia.org/wiki/SKI_combinator_calculus#Informal_description 
     for  reference) *)
  let eval = Semantics.eval in
  let open Syntax in
  assert (eval (app i x)                 = x);
  assert (eval (app (app k x) y)         = x);
  assert (eval (app (app (app s x) y) z) = (app (app x y) (app y z)))
```

## Additional References

- Harper explicitly connects binding scope with pointers in PFPL, tho I have not
  seen another implementation that takes this connection literally to bypass the
  usual pain of tedious renaming and inscrutable De Bruijn indices.

  > The crucial idea is that any use of an identifier should be understood as a
  > reference, or abstract pointer, to its binding. (PFPL, 2nd ed., p. 6)

- The implementation of ABTs in OCaml was informed by [Neel
  Krishnaswami](https://www.cl.cam.ac.uk/~nk480/)'s [post on
  ABTs](https://semantic-domain.blogspot.com/2015/03/abstract-binding-trees.html)
  (but is substantialy different).

- I discussed the idea of using `ref` cells to track binding scope in
  conversation with Callan McGill, and the representation of free and bound
  variables was influenced by his  post ["Locally
  Nameless"](https://boarders.github.io/posts/locally-nameless.html).
