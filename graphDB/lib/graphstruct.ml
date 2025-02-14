
(* Graph structures and bindings *)

type ('n, 'i) db_node = DBN of 'n * 'i
  [@@deriving show]
type ('n, 'r) db_rel = DBR of 'n * 'r * 'n
  [@@deriving show]
type ('n, 'i, 'r) db_graph = DBG of (('n, 'i) db_node list) * (('n, 'r) db_rel list)
  [@@deriving show]

let id_of_node (DBN(n, _nlb)) = n
let info_of_node (DBN(_n, nlb)) = nlb

let source_of_rel (DBR(s, _rlb, _t)) = s
let label_of_rel (DBR(_s, rlb, _t)) = rlb
let target_of_rel (DBR(_s, _rlb, t)) = t

let nodes_of_graph (DBG(ns,_rs)) = ns
let rels_of_graph (DBG(_ns,rs)) = rs

type nodeid = int
  [@@deriving show]
 

let empty_graph = DBG ([], [])

let add_nodes_to_graph new_nds (DBG (nds, rls)) = DBG (new_nds @ nds, rls)

(* An implicit assumption of the following is that the nodes adjacent to the relation exist in the graph *)
let add_rel_to_graph (DBG (nds, rls)) r = 
  let new_rls = if List.mem r rls then rls else (r::rls) in 
  DBG(nds, new_rls)

let find_node_with_id nid g = 
    List.find (fun (DBN(n, _)) -> n = nid) (nodes_of_graph g)
