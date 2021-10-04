(lang dune 2.8)
(name um-abt)

(generate_opam_files true)

(source (github shonfeder/um-abt))
(license MIT)

(authors "Shon Feder")
(maintainers "shon.feder@gmail.com")
(documentation "https://shonfeder.github.io/um-abt")

(package
 (name um-abt)
 (synopsis
  "An OCaml library implementing unifiable abstract binding trees (UABTs)")
 (description
  "um-abt provides an abstract binding tree (ABT) library following the
   principles of Robert Harper's 'Practical Foundations for Programming
   Languages'.

   The library uses immutable pointers to represent variable binding and extends
   ABTs with unification, providing unifiable abstract binding trees (UABTs).")
 (conflicts
  (result (< 1.5)))
 (depends
  (logs (>= 0.7.0))
  (sexplib (>= v0.14.0))

  ; preprocessing
  (ppx_expect (>= v0.14.1))
  (ppx_deriving (>= 5.2.1))
  (ppx_sexp_conv (>= v0.14.3))
  (logs-ppx (>= 0.2.0))

  ; tests
  (qcheck (and :with-test (>= 0.17)))
  (bos (and :with-test (>= 0.2.0)))
  (mdx (and :with-test (>= 1.10.1)))))
