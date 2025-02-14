
CHOSES A FAIRE APRES UN PULL

opam install . --deps-only &&
opam switch create . 5.0.0 &&
eval $(opam env) &&
dune build &&
dune exec Proj_GraphDB