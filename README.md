Groupe :
**BESSIERES Clément**
**VIGNERES Mathéo**

opam init
opam install ocaml-lsp-server -y &&
eval $(opam env)

opam install menhir -y &&
opam install ppx_deriving -y &&
opam install ocamlgraph -y &&
eval $(opam env)

dune build &&
dune exec Proj_GraphDB

puis

dune exec Proj_GraphDB i

---

Information pour le prof :

Utilisation d'assistant IA tel que chatGPT ou Grok pour écrire les commentaires.

Le projet s'exécute parfaitement.
le seul défaut est l'affichage des erreurs, qui ne fonctionne pas tout le temps.
Le projet est capable d'exécuter des requêtes miniGQL, puis de créer un graphe et une table en conséquence.

des tests ont étés fait dans le fichier interf.ml afin de tester chaque fonction au fûr et à mesure du développement. Cependant, nous avons décidés de retirer ces tests puisqu'ils ne respectent pas la consigne au sujet des tests, et que nous voulions laisser le fichier interf.ml d'origine.

Finalement, des tests du langage miniGQL ont étés écrits pour tester toutes les fonctionnalités de miniGQL.
les tests sont test1.q, test2.q et test3.q et fonctionnent parfaitement avec la commande dune exec Proj_GraphDB f test/test1.q
