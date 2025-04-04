
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



Utile pour moi pour plus tard :

let check_graph_types (DBG (ntdecls, rtdecls)) =
  let check_node_type (node : ('n, 'i) db_node) : (unit, string) result =
    (* Ici, vérifiez que le type des nœuds est valide *)
    (* Par exemple, vérifier que le type du nœud est bien du type 'label' et que ses attributs sont corrects *)
    match node with
    | (* Cas où le nœud est valide selon vos critères *)
      _ -> Ok ()
    | (* Cas où le nœud est invalide, renvoyer une erreur *)
      _ -> Error "Node type mismatch"
  in
  let check_rel_type (rel : ('n, 'r) db_rel) : (unit, string) result =
    (* Ici, vérifiez que le type des relations est valide *)
    (* Par exemple, vérifier que les types des relations entre les nœuds sont corrects *)
    match rel with
    | (* Cas où la relation est valide selon vos critères *)
      _ -> Ok ()
    | (* Cas où la relation est invalide, renvoyer une erreur *)
      _ -> Error "Relation type mismatch"
  in
  (* Vérification des nœuds *)
  let node_checks = List.map check_node_type ntdecls in
  let node_check_result = List.fold_left (fun acc res ->
    match acc, res with
    | Ok (), Ok () -> Ok ()
    | Error e, _ | _, Error e -> Error e
  ) (Ok ()) node_checks in

  (* Vérification des relations *)
  let rel_checks = List.map check_rel_type rtdecls in
  let rel_check_result = List.fold_left (fun acc res ->
    match acc, res with
    | Ok (), Ok () -> Ok ()
    | Error e, _ | _, Error e -> Error e
  ) (Ok ()) rel_checks in

  (* Combine les résultats des vérifications de nœuds et de relations *)
  match node_check_result, rel_check_result with
  | Ok (), Ok () -> Ok ()
  | Error e, _ | _, Error e -> Error e