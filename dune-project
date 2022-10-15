(lang dune 3.4)

(name antireduce_graphs)

(generate_opam_files true)

(package
 (name antireduce_graphs)
 (version "0.1.0")
 (synopsis
  "Simple undirected node-labelled graph construction primitives for antireduce integration")
 (description
  "A companion package to antireduce implementing one domain of primitives for use in polymorphic lambda calculus representations")
 (depends core antireduce ppx_jane ppx_sexp_conv ppx_yojson_conv)
 (license "MIT")
 (authors "Eli Whitehouse <eliw55@gmail.com>")
 (maintainers "Eli Whitehouse <eliw55@gmail.com>")
 (source
  (github shlomenu/antireduce-graphs))
 (bug_reports "https://github.com/shlomenu/antireduce-graphs/issues"))
