
CHOSES A FAIRE APRES UN PULL

opam install . --deps-only
opam switch create . 5.0.0  # (si nécessaire)
eval $(opam env)
dune build
dune exec graphDB  # (pour tester)