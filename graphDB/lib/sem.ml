(* Semantics of instructions *)
open Lang
open Graphstruct
open Instr

(* State of the program, essentially a graph structure and a binding in form of a table,
   and as convenience info an overapproximation of the maximal node number
   allocated in the graph (could in principle be recomputed each time)
   Nodes have a unique identifier (an int) which is incremented when creating new nodes.
   When deleting nodes, the max node number is currently not decremented, 
   thus does not reflect the number of nodes in the graph, but one could think
   of a garbage collector when running out of node identifiers.
*)

(* Naive implementation of bindings as tables, ie. 
   a heading (variable list 'v list) and a list of lines containing nodes 
   that each have the same length as the variable list *)

type ('v, 'n) table = Table of 'v list * 'n list list
  [@@deriving show]

type vname_nodeid_table = (vname, nodeid) table
  [@@deriving show]

let empty_table = Table([], [[]])

(* Add a single variable v, bound to a single node n, to a table,
   as during node creation (old interpretation, now superseded, 
   see create_node and add_var_mult_nodes_to_table) *)
let add_var_single_node_to_table v n (Table (vns, lns)) = 
    Table (v::vns, List.map (fun ln -> n::ln) lns)

(* Add multiple nodes contained in ns for a new variable v to a table,
   one node per line. ns and lns have to have the same length. *)
let add_var_mult_nodes_to_table v ns (Table (vns, lns)) = 
  Table (v::vns, List.map2 (fun n ln -> n::ln) ns lns)

type attrib_val = fieldname * value [@@deriving show]
type attrib_struct = label * (attrib_val list) [@@deriving show]
type db_graph_struct = (Graphstruct.nodeid, attrib_struct, label) Graphstruct.db_graph [@@deriving show]
type state = State of db_graph_struct * (vname, nodeid) table * nodeid [@@deriving show]

let initial_state = State(empty_graph, empty_table, 0)

let create_node v lb (State (g, tab, mn)) = 
  let Table (_vns, lns) = tab in 
  let new_node_ids = List.init (List.length lns) (fun i -> mn + i) in 
  let new_nodes = List.init (List.length lns) (fun i -> DBN (mn + i, (lb, []))) in
  let new_tab = add_var_mult_nodes_to_table v new_node_ids tab in
  let new_graph = add_nodes_to_graph new_nodes g in 
  State (new_graph, new_tab, mn + 1)

(* --- Fonctions auxiliaires --- *)

(* 
 * find_index: Trouve l’indice du premier élément satisfaisant un prédicat dans une liste.
 * Entrée: p ('a -> bool) - Prédicat à tester sur chaque élément.
 *         lst ('a list) - Liste dans laquelle chercher.
 * Sortie: int option - L’indice de l’élément (Some i) ou None si non trouvé.
 *)
let rec find_index p lst =
  let rec aux i = function
    | [] -> None
    | x :: xs -> if p x then Some i else aux (i + 1) xs
  in
  aux 0 lst

(* 
 * get_nodes_by_label: Récupère les identifiants des nœuds ayant un label donné.
 * Entrée: lb (label) - Le label recherché.
 *         g (db_graph_struct) - Le graphe.
 * Sortie: nodeid list - Liste des identifiants des nœuds avec ce label.
 *)
let get_nodes_by_label lb (DBG (nodes, _rels)) =
  List.filter_map (fun (DBN (nid, (lbl, _attrs))) -> if lbl = lb then Some nid else None) nodes

(* 
 * get_node_attrs: Récupère les attributs d’un nœud à partir de son identifiant.
 * Entrée: nid (nodeid) - Identifiant du nœud.
 *         g (db_graph_struct) - Le graphe contenant les nœuds.
 * Sortie: attrib_val list - Liste des attributs du nœud.
 * Exception: Failwith si le nœud n’existe pas.
 *)
let get_node_attrs nid g =
  let DBN (_, (_, attrs)) = find_node_with_id nid g in
  attrs

(* 
 * eval_expr: Évalue une expression dans le contexte d’une table et d’une ligne.
 * Entrée: tab (vname_nodeid_table) - La table de valuations.
 *         row (nodeid list) - Une ligne de la table (valeurs des variables).
 *         g (db_graph_struct) - Le graphe pour accéder aux attributs.
 *         e (expr) - L’expression à évaluer.
 * Sortie: value - La valeur calculée de l’expression.
 * Exception: Failwith si une variable ou un attribut est indéfini.
 *)
let rec eval_expr tab row g = function
  | Const v -> v
  | AttribAcc (vn, fn) ->
      let Table (vns, _) = tab in
      (match find_index ((=) vn) vns with
       | Some i ->
           let nid = List.nth row i in
           let attrs = get_node_attrs nid g in
           (match List.assoc_opt fn attrs with
            | Some v -> v
            | None -> failwith ("Attribute " ^ fn ^ " not defined for variable " ^ vn))
       | None -> failwith ("Variable " ^ vn ^ " not in table"))
  | BinOp (bop, e1, e2) ->
      let v1 = eval_expr tab row g e1 in
      let v2 = eval_expr tab row g e2 in
      match bop with
      | BArith BAadd -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 + i2) | _ -> failwith "Invalid types for +")
      | BArith BAsub -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 - i2) | _ -> failwith "Invalid types for -")
      | BArith BAmul -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 * i2) | _ -> failwith "Invalid types for *")
      | BArith BAdiv -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 / i2) | _ -> failwith "Invalid types for /")
      | BArith BAmod -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 mod i2) | _ -> failwith "Invalid types for mod")
      | BCompar BCeq -> BoolV (v1 = v2)
      | BCompar BCge -> (match v1, v2 with IntV i1, IntV i2 -> BoolV (i1 >= i2) | _ -> failwith "Invalid types for >=")
      | BCompar BCgt -> (match v1, v2 with IntV i1, IntV i2 -> BoolV (i1 > i2) | _ -> failwith "Invalid types for >")
      | BCompar BCle -> (match v1, v2 with IntV i1, IntV i2 -> BoolV (i1 <= i2) | _ -> failwith "Invalid types for <=")
      | BCompar BClt -> (match v1, v2 with IntV i1, IntV i2 -> BoolV (i1 < i2) | _ -> failwith "Invalid types for <")
      | BCompar BCne -> BoolV (v1 <> v2)
      | BLogic BLand -> (match v1, v2 with BoolV b1, BoolV b2 -> BoolV (b1 && b2) | _ -> failwith "Invalid types for &&")
      | BLogic BLor -> (match v1, v2 with BoolV b1, BoolV b2 -> BoolV (b1 || b2) | _ -> failwith "Invalid types for ||")

(* 
 * add_rels_to_graph: Ajoute une liste de relations au graphe.
 * Entrée: rels (db_rel list) - Les relations à ajouter.
 *         g (db_graph_struct) - Le graphe initial.
 * Sortie: db_graph_struct - Le graphe mis à jour.
 *)
let add_rels_to_graph rels g =
  List.fold_left add_rel_to_graph g rels

(* 
 * remove_node_from_graph: Supprime un nœud et ses relations associées du graphe.
 * Entrée: nid (nodeid) - L’identifiant du nœud à supprimer.
 *         g (db_graph_struct) - Le graphe initial.
 * Sortie: db_graph_struct - Le graphe mis à jour.
 *)
let remove_node_from_graph nid (DBG (nodes, rels)) =
  let new_nodes = List.filter (fun (DBN (n, _)) -> n <> nid) nodes in
  let new_rels = List.filter (fun (DBR (s, _, t)) -> s <> nid && t <> nid) rels in
  DBG (new_nodes, new_rels)

(* 
 * remove_rels_from_graph: Supprime une liste de relations spécifiques du graphe.
 * Entrée: rels (db_rel list) - Les relations à supprimer.
 *         g (db_graph_struct) - Le graphe initial.
 * Sortie: db_graph_struct - Le graphe mis à jour.
 *)
let remove_rels_from_graph rels (DBG (nodes, existing_rels)) =
  let new_rels = List.filter (fun r -> not (List.mem r rels)) existing_rels in
  DBG (nodes, new_rels)

(* 
 * update_node_attrs: Met à jour les attributs d’un nœud dans le graphe.
 * Entrée: nid (nodeid) - L’identifiant du nœud à mettre à jour.
 *         fn (fieldname) - Le nom de l’attribut à modifier.
 *         v (value) - La nouvelle valeur.
 *         g (db_graph_struct) - Le graphe initial.
 * Sortie: db_graph_struct - Le graphe mis à jour.
 *)
let update_node_attrs nid fn v (DBG (nodes, rels)) =
  let new_nodes = List.map (fun (DBN (n, (lbl, attrs))) ->
    if n = nid then
      let new_attrs = (fn, v) :: List.filter (fun (f, _) -> f <> fn) attrs in
      DBN (n, (lbl, new_attrs))
    else DBN (n, (lbl, attrs))
  ) nodes in
  DBG (new_nodes, rels)

(* Execute an instruction, updating the state *)
let exec_instr (State (g, tab, mn) as s) = function
  | IActOnNode (CreateAct, v, lb) -> create_node v lb s
  | IActOnNode (MatchAct, v, lb) ->
      let Table (vns, lns) = tab in
      let matching_nodes = get_nodes_by_label lb g in
      let new_lns = List.concat_map (fun ln -> List.map (fun n -> n :: ln) matching_nodes) lns in
      State (g, Table (v::vns, new_lns), mn)
  | IActOnRel (CreateAct, sv, lb, tv) ->
      let Table (vns, lns) = tab in
      (match find_index ((=) sv) vns, find_index ((=) tv) vns with
       | Some si, Some ti ->
           let new_rels = List.map (fun ln -> DBR (List.nth ln si, lb, List.nth ln ti)) lns in
           let new_graph = add_rels_to_graph new_rels g in
           State (new_graph, tab, mn)
       | _ -> failwith "Variables not in table")
  | IActOnRel (MatchAct, sv, lb, tv) ->
      let Table (vns, lns) = tab in
      (match find_index ((=) sv) vns, find_index ((=) tv) vns with
       | Some si, Some ti ->
           let DBG (_, rels) = g in
           let valid_lns = List.filter (fun ln ->
             let s = List.nth ln si in
             let t = List.nth ln ti in
             List.exists (fun (DBR (src, rlbl, tgt)) -> src = s && rlbl = lb && tgt = t) rels
           ) lns in
           State (g, Table (vns, valid_lns), mn)
       | _ -> failwith "Variables not in table")
  | IDeleteNode v ->
      let Table (vns, lns) = tab in
      (match find_index ((=) v) vns with
       | Some i ->
           let nodes_to_remove = List.map (fun ln -> List.nth ln i) lns in
           let new_graph = List.fold_left (fun g nid -> remove_node_from_graph nid g) g nodes_to_remove in
           let new_vns = List.filter ((<>) v) vns in
           let new_lns = List.map (fun ln -> List.filteri (fun j _ -> j <> i) ln) lns in
           State (new_graph, Table (new_vns, new_lns), mn)
       | None -> failwith "Variable not in table")
  | IDeleteRel (sv, lb, tv) ->
      let Table (vns, lns) = tab in
      (match find_index ((=) sv) vns, find_index ((=) tv) vns with
       | Some si, Some ti ->
           let rels_to_remove = List.map (fun ln -> DBR (List.nth ln si, lb, List.nth ln ti)) lns in
           let new_graph = remove_rels_from_graph rels_to_remove g in
           State (new_graph, tab, mn)
       | _ -> failwith "Variables not in table")
  | IReturn vs ->
      let Table (vns, lns) = tab in
      let indices = List.map (fun v ->
        match find_index ((=) v) vns with
        | Some i -> i
        | None -> failwith ("Variable " ^ v ^ " not in table")
      ) vs in
      let new_lns = List.map (fun ln -> List.map (fun i -> List.nth ln i) indices) lns in
      State (g, Table (vs, new_lns), mn)
  | IWhere e ->
      let Table (vns, lns) = tab in
      let new_lns = List.filter (fun ln ->
        match eval_expr tab ln g e with
        | BoolV true -> true
        | BoolV false -> false
        | _ -> failwith "Where expression must evaluate to boolean"
      ) lns in
      State (g, Table (vns, new_lns), mn)
  | ISet (vn, fn, e) ->
      let Table (vns, lns) = tab in
      (match find_index ((=) vn) vns with
       | Some i ->
           let nodes_to_update = List.map (fun ln -> List.nth ln i) lns in
           (* On évalue l’expression avec la première ligne pour simplifier *)
           let value = eval_expr tab (List.hd lns) g e in
           let new_graph = List.fold_left (fun g nid -> update_node_attrs nid fn value g) g nodes_to_update in
           State (new_graph, tab, mn)
       | None -> failwith ("Variable " ^ vn ^ " not in table"))

let exec (NormProg (_tps, NormQuery instrs)) = 
  List.fold_left exec_instr initial_state instrs