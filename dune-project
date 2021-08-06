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
  "An OCaml library implementing abstract binding trees (ABTs)")
 (description
  "An ABT library consistent with the interface defined in Robert Harper's
   'Practical Foundations for Programming Languages', using immutable
   pointers to for varibale binding.")
 (depends
  (bos (>= 0.2.0))
  (ppx-logs (>= 0.2.0))
  (ppx_expect (>= v0.14.1))
  (ppx_deriving (>= 5.2.1))
  (qcheck (and :with-test (>= 0.17)))))
