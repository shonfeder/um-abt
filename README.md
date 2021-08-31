# um-abt

[![build](https://github.com/shonfeder/um-abt/actions/workflows/main.yml/badge.svg)](https://github.com/shonfeder/um-abt/actions/workflows/main.yml)
<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->
**Table of Contents**

- [um-abt](#um-abt)
    - [Overview](#overview)
        - [Documentation](#documentation)
        - [Aims](#aims)
        - [Features](#features)
        - [Installation](#installation)
    - [Synopsis](#synopsis)
        - [An ABT for the λ-calculus](#an-abt-for-the-λ-calculus)
        - [Unification over λ-calculus terms](#unification-over-λ-calculus-terms)
    - [Additional References](#additional-references)

<!-- markdown-toc end -->

## Overview

`um-abt` is OCaml library implementing abstract binding trees (ABTs) exhibiting
the properties defined in [Robert Harper](https://www.cs.cmu.edu/~rwh/pfpl/)'s
[Practical Foundations for Programming
Labguages](https://www.cs.cmu.edu/~rwh/pfpl/) (PFPL).

### Documentation

- [API Documentation](https://shonfeder.github.io/um-abt/um-abt/Abt/index.html)
- [Synposis](#synopsis)
- [Examples](https://github.com/shonfeder/um-abt/blob/trunk/test/example/example.ml)

### Aims

This library aims for the following qualities:

1. It should be correct.
2. It should be well tested, to ensure its correctness.
3. It should be easy to use.
4. It should be well documented.

### Features

This ABT library has two distinctive (afaik) features:

1. The library augments the binding functionality of the ABT approach with
   **unification modulo ɑ-equivalence**. We might therefore describe this
   library as an implementation of *unifiable* abstract binding trees (or
   UABTs): where ABTs provide a general and reusable system for variable
   binding, UABTs add a general and reusable system for nominal unification.

   Unification is lovely and not used nearly enough, imo.

2. The library implements variable binding via (what we might call) **binding by
   reference**; i.e., variable binding is recorded in the pointer structure of
   by way of "immutable" reference cells. This is somewhat of an experiment:
   being unaware of other implementations using this approach, I worked out the
   details as I went. So far, it seems to have yielded [trivial ɑ-equivalence
   and substitution algorithms, and enabled nominal unification][], without
   requiring any bureaucratic fiddling with renaming, variable permutations, or
   fresh variables. 
   
**Caveat emptor**: I am not an academic PLT researcher and this library has not
yet been used extensively.

[trivial ɑ-equivalence]: https://github.com/shonfeder/um-abt/blob/trunk/lib/abt.ml
[HOAS]: https://en.wikipedia.org/wiki/Higher-order_abstract_syntax

### Installation

The latest released version can be installed with
[opam](https://opam.ocaml.org/doc/Install.html#Binary-distribution):

``` sh
opam install um-abt
```

To install the head of development

``` sh
opam pin git@github.com:shonfeder/um-abt.git
```

## Synopsis

The following short examples help illustrate use of the library. For more
extensive examples, see
[test/example/example.ml](https://github.com/shonfeder/um-abt/blob/trunk/test/example/example.ml).

### An ABT for the λ-calculus

Here is a short example showing a naive implementation of the untyped lambda
calculus using `um-abt`.

ABTs representing the syntax of a language are produced by applying the
`Abt.Make` functor to a module implementing the `Operator` specification.

```ocaml
module Syntax = struct

  (* Define the usual operators, but without the variables, since we get those free *)
  module O = struct
      type 'a t =
      | App of 'a * 'a
      | Lam of 'a
      [@@deriving eq, map, fold]

      let to_string : string t -> string = function
      | App (l, m) -> Printf.sprintf "(%s %s)" l m
      | Lam abs    -> Printf.sprintf "(λ%s)" abs
  end

  (* Generate the syntax, which will include a type [t] of the ABTs over the operators **)
  include Abt.Make (O)

  (* Define some constructors to ensure correct construction *)

  let app m n : t =
    (* [op] lifts an operator into an ABT *)
    op (App (m, n))

  let lam x m : t =
    (* ["x" #. scope] binds all free variables named "x" in the [scope] *)
    op (Lam (x #. m))
end
```

The generated ABT will have the following form:

```ocaml skip
type t = private
  | Var of Abt.Var.t
  | Bnd of Abt.Var.binding * t
  | Opr of t O.t
```

Most of the values required by the `Operator` specification can be derived using
[`ppx_deriving`](https://github.com/ocaml-ppx/ppx_deriving). So all that is
usually required is to define a datatype representing the operators and their
arities.

After the ABT is generated However, it is recommended that one also define constructors making it
more convenient and safer to construct terms of the language.

The `private` annotation indicates that you can use pattern matching to
deconstruct the ABT, but you cannot construct new values without using the
supplied combinators. This ensures essential invariants are preserved. E.g., it
is impossible to construct a binding in which the expected variables are not
bound in the term in scope.

For a more perspicuous view of our produce, let's define the [SKI
combinators](https://en.wikipedia.org/wiki/SKI_combinator_calculus) and see what
they look like when printed in the usual notation:

```ocaml
(* [v x] is a free variable named "x" *)
let x, y, z = Syntax.(v "x", v "y", v "z")

let s = Syntax.(lam "x" (lam "y" (lam "z" (app (app x y) (app y z)))))
let k = Syntax.(lam "x" (lam "y" x))
let i = Syntax.(lam "x" x)

let () =
  assert (Syntax.to_string s = "(λx.(λy.(λz.((x y) (y z)))))");
  assert (Syntax.to_string k = "(λx.(λy.x))");
  assert (Syntax.to_string i = "(λx.x)");
```

Note that equality between ABTs is defined in terms of ɑ-equivalence, so we can
define the `i` using any variable, and it will be equivalent:

```ocaml
let () =
  assert Syntax.(equal i (lam "y" y))
```


Now let's define reduction, using the API provided by our generated `Syntax`.
`Syntax` modules expose `private` value constructors, which provide a
pattern-matching based interface for destructuring ABTs, but prevents
constructing new ABTs directly. This gives us the convenience of a pattern
matching API without compromising the integrity of the ABT representation by
allowing ill-formed structures.

```ocaml
open Syntax

let rec eval : t -> t =
 fun t ->
  match t with
  | Opr (App (m, n)) -> apply (eval m) (eval n)
  (* No other terms can be evaluated *)
  | _                -> t

and apply : t -> t -> t =
 fun m n ->
  match m with
  | Bnd (bnd, t)  -> subst bnd ~value:n t
  | Opr (Lam bnd) -> eval (apply bnd n)
  (* otherwise the application can't be evaluated *)
  | _             -> app m n
```

Finally, let's illustrate the correctness of our implementation with a few
simple evaluations, demonstrating that our SKI combinators behave as expected:

``` ocaml
let () =
  (* Let equality be ɑ-equivalence on our syntax for the following examples *)
  let (=) = Syntax.equal in
  let open Syntax in
  assert (eval (app i x)                 = x);
  assert (eval (app (app k x) y)         = x);
  assert (eval (app (app (app s x) y) z) = (app (app x y) (app y z)))
```

(See
<https://en.wikipedia.org/wiki/SKI_combinator_calculus#Informal_description> for
reference.)

### Unification over λ-calculus terms

The ABTs produced by applying the `Abt.Make` functor to an `Operator`
implementation support first-order, syntactic unification modulo ɑ-equivalence.

- Unification is (currently) limited to first-order, because there is no support
  for variables standing for operators.
- Unification is (currently) syntactic, because we do not perform any evaluation
  to determine if two ABTs can be unified.
- Unification is modulo ɑ-equivalence, because two ɑ-equivalent ABTs are
  considered equal during unification.

``` ocaml
let () =
  let open Syntax in

  (* The generated [Syntax] module includes a [Unification] submodule

     - the [=?=] operator checks for unifiability
     - the [=.=] operator gives an [Ok] result with the unified term, if its operands unify,
       or else an [Error] indicating why the unification failed
     - the [unify] function is like [=.=], but it also gives the substitution used to produce
       a unified term *)
  let ((=?=), (=.=), unify) = Unification.((=?=), (=.=), unify) in

  (* A free variable will unify with anything *)
  assert (v "X" =?= s);

  (* Again, unification is modulo ɑ-equivalence *)
  assert (lam "y" (lam "x" y) =?= lam "x" (lam "y" x));

  (* Here we unify the free variable "M" with the body of the [k] combinator, 
     note that the nominal unification is modulo bound variables: *)
  let unified_term = (lam "z" (v "M") =.= k) |> Result.get_ok in
  assert (to_string unified_term = "(λz.(λy.z))");

  (* The substitution allows retrieval the bound values of the free variables *)
  let _, substitution = unify (lam "x" (v "M")) k |> Result.get_ok in
  assert (Unification.Subst.to_string substitution = "[ M -> (λy.x) ]")
```

## Additional References

- Harper explicitly connects binding scope with pointers in PFPL (tho I have not
  seen another functional implementation that takes this connection literally):

  > The crucial idea is that any use of an identifier should be understood as a
  > reference, or abstract pointer, to its binding. (PFPL, 2nd ed., p. 6)

- I discussed the idea of using `ref` cells to track binding scope in
  conversation with Callan McGill, and the representation of free and bound
  variables was influenced by his post ["Locally
  Nameless"](https://boarders.github.io/posts/locally-nameless.html).

- My initial implementation of an ABT library was informed by [Neel
  Krishnaswami](https://www.cl.cam.ac.uk/~nk480/)'s [post on
  ABTs](https://semantic-domain.blogspot.com/2015/03/abstract-binding-trees.html).
  There are still some aspects of that approach that show up here.

- I consulted [Christian Urban](https://nms.kcl.ac.uk/christian.urban/)'s paper
  [Nominal Unification Revisited](https://arxiv.org/pdf/1012.4890.pdf) and
  Urban, Pitts, and Gabby's [Nominal
  Unification](http://gabbay.org.uk/papers/nomu-jv.pdf)  for guidance on the
  harrier bits of unification modulo ɑ-equivalence, tho this library does not
  currently take advantage of the strategy of nominal permutations described
  there.
