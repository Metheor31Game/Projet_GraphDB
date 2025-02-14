
CHOSES A FAIRE APRES UN PULL
opam install dune &&
opam install . --deps-only &&
opam install core yojson menhir &&
opam install ppx_deriving &&
opam install ocamlgraph &&
opam switch create . 5.0.0 &&
eval $(opam env) &&
dune build &&
dune exec Proj_GraphDB