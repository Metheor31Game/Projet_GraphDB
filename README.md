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

OU

opam init
opam install ocaml-lsp-server -y
eval $(opam env)

opam install menhir -y
opam install ppx_deriving -y
opam install ocamlgraph -y
eval $(opam env)

dune build
dune exec Proj_GraphDB

puis

dune exec Proj_GraphDB i

Information pour le prof :
Utilisation d'assistant IA tel que chatGPT ou Grok pour écrire les commentaires et préparer des tests pour les fonctions.
