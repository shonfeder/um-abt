# um-abt

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->
**Table of Contents**

- [um-abt](#um-abt)
    - [Features](#features)
    - [Examples](#examples)
        - [The simply typed lambda calculus](#the-simply-typed-lambda-calculus)
        - [Unification](#unification)
    - [Additional References](#additional-references)

<!-- markdown-toc end -->

An OCaml library implementing abstract binding trees (ABTs) exhibiting with the
properties defined in [Robert Harper](https://www.cs.cmu.edu/~rwh/pfpl/)'s
[Practical Foundations for Programming Labguages](https://www.cs.cmu.edu/~rwh/pfpl/)
(PFPL).

## Features

This ABT library has two distinctive (afaik) features:

1. The library augments the binding functionality of the ABT approach with
   general syntactic (perhaps later also equational) unification. We might
   therefore describe this library as an implentation of *unifiable* abstract
   binding trees (or UABTs). ABTs provide a generalized a reusable system for
   variable binding for any language implemented in its terms. UABTs provide --
   in addition -- a generalized, reusable system for (first-order, syntactic)
   unification for any language implemented in *its* terms.

   Unification is lovely and not used nearly enough, imo.

2. It implements variable binding via (what we might call) *binding by
   reference*; i.e., variable binding is implemented by way of "immutable"
   reference cells. I believe the advantages of this approach to include:

   - a trivial algorithm for computing ɑ-equivalence
   - neutralization of the usual problem of renaming bound variables
   - the representation is easy to read, in contrast with De Bruijn indices,
     and, even more important, there's no tedious bookkeeping required during
     substitution.
   - the representation is trivial to inspect and manipulate, in contrast with
     [HOAS][]

   However, I suspect this approach lacks the safety and formal elegance of HOAS
   or [NbE](https://en.wikipedia.org/wiki/Normalisation_by_evaluation). The
   approach used here is also dependent on OCaml's definition of physical
   equality to identify `ref` cells, and on MLs ability to ensure that the
   references are immutable via type abstraction.


[HOAS]: https://en.wikipedia.org/wiki/Higher-order_abstract_syntax

## Examples

### The simply typed lambda calculus

Here is a short example showing a naive implementation of the simply typed
lambda calculus using `um-abt`.

Let's start with the syntax:

```ocaml
module Syntax = struct

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
```

The functor `Abt.Make` is applied to an operator satisfying the `Operator`
interface to produce a ABT representing the syntax of the simply typed lambda
calculus.

To make this more concrete, let's define the [SKI
combinators](https://en.wikipedia.org/wiki/SKI_combinator_calculus) and see what
they look like printed into the usual lambda calculus notation:

```ocaml
(* [v x] is a free variable named "x" *)
let x, y, z = Syntax.(v "x", v "y", v "z")

let s = Syntax.(lam "x" (lam "y" (lam "z" (app (app x y) (app y z)))))
let k = Syntax.(lam "x" (lam "y" x))
let i = Syntax.(lam "x" x)

let () =
  (* Here's what the combinators look like as strings *)
  assert (Syntax.to_string s = "(λx.(λy.(λz.((x y) (y z)))))");
  assert (Syntax.to_string k = "(λx.(λy.x))");
  assert (Syntax.to_string i = "(λx.x)")
```


Note that equality between ABTs is defined in terms of ɑ-equivalence, so we can
define the `i` using any variable, and it will be equivalent:

```ocaml
let () =
  assert Syntax.(equal i (lam "y" y))
```


Now let's define our semantics, using the simple API provided by our generated
`Syntax`. The key functions used are

- `subst` to substitute values for bound variables, and
- `case` to do case-based analysis of expressions in the ABT

```ocaml
module Semantics = struct

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
```

Finally, let's illustrate the correctness of our implementation with a few
simple evaluations, demonstrating that our SKI combinators behave as expected:

``` ocaml


let () =
  (* Let's fix our equality to be in terms of ɑ-equivalent ABTs *)
  let (=) = Syntax.equal in
  let eval = Semantics.eval in
  let open Syntax in
  assert (eval (app i x)                 = x);
  assert (eval (app (app k x) y)         = x);
  assert (eval (app (app (app s x) y) z) = (app (app x y) (app y z)))
```

(See https://en.wikipedia.org/wiki/SKI_combinator_calculus#Informal_description
for reference.)

### Unification

TODO

## Additional References

- Harper explicitly connects binding scope with pointers in PFPL, tho I have not
  seen another implementation that takes this connection literally to bypass the
  usual pain of tedious renaming and inscrutable De Bruijn indices.

  > The crucial idea is that any use of an identifier should be understood as a
  > reference, or abstract pointer, to its binding. (PFPL, 2nd ed., p. 6)

- I discussed the idea of using `ref` cells to track binding scope in
  conversation with Callan McGill, and the representation of free and bound
  variables was influenced by his  post ["Locally
  Nameless"](https://boarders.github.io/posts/locally-nameless.html).

- The implementation of ABTs in OCaml was informed by [Neel
  Krishnaswami](https://www.cl.cam.ac.uk/~nk480/)'s [post on
  ABTs](https://semantic-domain.blogspot.com/2015/03/abstract-binding-trees.html)
  (but is substantialy different).
