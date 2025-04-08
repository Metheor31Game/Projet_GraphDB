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


(** 
 * find_index - Recherche l'index d'un élément satisfaisant un prédicat dans une liste.
 *
 * @description 
 * Cette fonction récursive trouve le premier index d'un élément dans une liste qui satisfait un prédicat donné. 
 * Elle utilise une fonction auxiliaire interne pour parcourir la liste avec un compteur d'index.
 *
 * @param p Le prédicat à appliquer à chaque élément, de type ['a -> bool].
 * @param lst La liste dans laquelle chercher, de type ['a list].
 *
 * @return Retourne un résultat de type [int option] :
 *         - [Some i] si un élément satisfaisant le prédicat est trouvé à l'index i.
 *         - [None] si aucun élément ne satisfait le prédicat.
 *
 * @type ['a -> 'a list -> int option]
 *
 * @var i Compteur d'index dans la fonction auxiliaire, de type [int].
 * @var aux Fonction auxiliaire récursive pour parcourir la liste, de type [int -> 'a list -> int option].
 *)
let rec find_index p lst =
  (* Fonction auxiliaire pour parcourir la liste avec un compteur *)
  let rec aux i = function
    | [] -> None  (* Liste vide : aucun élément trouvé *)
    | x :: xs -> if p x then Some i else aux (i + 1) xs  (* Retourne i si p(x) est vrai, sinon continue *)
  in
  aux 0 lst  (* Démarre avec l'index 0 *)

(** 
 * get_nodes_by_label - Récupère les identifiants des nœuds ayant une étiquette spécifique.
 *
 * @description 
 * Cette fonction extrait les identifiants des nœuds d'un graphe qui portent une étiquette donnée, en 
 * filtrant les nœuds du graphe.
 *
 * @param lb L'étiquette à rechercher, de type [string].
 * @param g Le graphe contenant les nœuds, de type [Graphstruct.db_graph].
 *
 * @return Retourne une liste d'identifiants de nœuds, de type [string list].
 *
 * @type [string -> Graphstruct.db_graph -> string list]
 *)
let get_nodes_by_label lb (DBG (nodes, _rels)) =
  (* Filtre les nœuds et extrait les identifiants correspondants à l'étiquette *)
  List.filter_map (fun (DBN (nid, (lbl, _attrs))) -> if lbl = lb then Some nid else None) nodes

(** 
 * get_node_attrs - Récupère les attributs d'un nœud à partir de son identifiant.
 *
 * @description 
 * Cette fonction recherche un nœud dans un graphe par son identifiant et retourne ses attributs. Elle 
 * repose sur find_node_with_id pour localiser le nœud.
 *
 * @param nid L'identifiant du nœud, de type [string].
 * @param g Le graphe contenant le nœud, de type [Graphstruct.db_graph].
 *
 * @return Retourne la liste des attributs du nœud, de type [(string * Lang.value) list].
 *
 * @type [string -> Graphstruct.db_graph -> (string * Lang.value) list]
 *)
let get_node_attrs nid g =
  (* Recherche le nœud et extrait ses attributs *)
  let DBN (_, (_, attrs)) = find_node_with_id nid g in
  attrs

(** 
 * eval_expr - Évalue une expression MiniGQL dans un contexte donné.
 *
 * @description 
 * Cette fonction récursive évalue une expression MiniGQL (constante, accès à un attribut ou opération 
 * binaire) en utilisant une table de variables, une ligne de données et un graphe. Elle lève une 
 * exception failwith en cas d'erreur (variable ou attribut non défini, types invalides).
 *
 * @param tab La table contenant les variables et lignes, de type [Lang.table].
 * @param row Une ligne de données (liste d'identifiants), de type [string list].
 * @param g Le graphe de données, de type [Graphstruct.db_graph].
 * @param expr L'expression à évaluer, de type [Lang.expr].
 *
 * @return Retourne la valeur calculée, de type [Lang.value].
 *
 * @type [Lang.table -> string list -> Graphstruct.db_graph -> Lang.expr -> Lang.value]
 *
 * @exception failwith Levée avec un message en cas de variable ou attribut non défini, ou de types incompatibles.
 *
 * @var vns Liste des noms de variables dans la table, de type [string list].
 * @var i Index de la variable dans la table, de type [int].
 * @var nid Identifiant du nœud associé à la variable, de type [string].
 * @var attrs Attributs du nœud, de type [(string * Lang.value) list].
 * @var v1 Valeur de la première sous-expression, de type [Lang.value].
 * @var v2 Valeur de la seconde sous-expression, de type [Lang.value].
 *)
let rec eval_expr tab row g = function
  | Const v -> v  (* Une constante retourne directement sa valeur *)
  | AttribAcc (vn, fn) ->
      let Table (vns, _) = tab in
      (* Recherche l'index de la variable dans la table *)
      (match find_index ((=) vn) vns with
       | Some i ->
           let nid = List.nth row i in  (* Récupère l'identifiant du nœud à cet index *)
           let attrs = get_node_attrs nid g in  (* Récupère les attributs du nœud *)
           (match List.assoc_opt fn attrs with
            | Some v -> v  (* Retourne la valeur de l'attribut si trouvé *)
            | None -> failwith ("Attribute " ^ fn ^ " not defined for variable " ^ vn))
       | None -> failwith ("Variable " ^ vn ^ " not in table"))
  | BinOp (bop, e1, e2) ->
      let v1 = eval_expr tab row g e1 in  (* Évalue la première sous-expression *)
      let v2 = eval_expr tab row g e2 in  (* Évalue la seconde sous-expression *)
      match bop with
      | BArith BAadd -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 + i2) | _ -> failwith "Invalid types for +")
      | BArith BAsub -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 - i2) | _ -> failwith "Invalid types for -")
      | BArith BAmul -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 * i2) | _ -> failwith "Invalid types for *")
      | BArith BAdiv -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 / i2) | _ -> failwith "Invalid types for /")
      | BArith BAmod -> (match v1, v2 with IntV i1, IntV i2 -> IntV (i1 mod i2) | _ -> failwith "Invalid types for mod")
      | BCompar BCeq -> BoolV (v1 = v2)  (* Égalité entre deux valeurs *)
      | BCompar BCge -> (match v1, v2 with IntV i1, IntV i2 -> BoolV (i1 >= i2) | _ -> failwith "Invalid types for >=")
      | BCompar BCgt -> (match v1, v2 with IntV i1, IntV i2 -> BoolV (i1 > i2) | _ -> failwith "Invalid types for >")
      | BCompar BCle -> (match v1, v2 with IntV i1, IntV i2 -> BoolV (i1 <= i2) | _ -> failwith "Invalid types for <=")
      | BCompar BClt -> (match v1, v2 with IntV i1, IntV i2 -> BoolV (i1 < i2) | _ -> failwith "Invalid types for <")
      | BCompar BCne -> BoolV (v1 <> v2)  (* Différence entre deux valeurs *)
      | BLogic BLand -> (match v1, v2 with BoolV b1, BoolV b2 -> BoolV (b1 && b2) | _ -> failwith "Invalid types for &&")
      | BLogic BLor -> (match v1, v2 with BoolV b1, BoolV b2 -> BoolV (b1 || b2) | _ -> failwith "Invalid types for ||")

(** 
 * add_rels_to_graph - Ajoute une liste de relations à un graphe.
 *
 * @description 
 * Cette fonction ajoute séquentiellement une liste de relations à un graphe existant en utilisant une 
 * réduction gauche avec add_rel_to_graph.
 *
 * @param rels La liste des relations à ajouter, de type [Graphstruct.db_rel list].
 * @param g Le graphe initial, de type [Graphstruct.db_graph].
 *
 * @return Retourne le graphe mis à jour, de type [Graphstruct.db_graph].
 *
 * @type [Graphstruct.db_rel list -> Graphstruct.db_graph -> Graphstruct.db_graph]
 *)
let add_rels_to_graph rels g =
  (* Ajoute chaque relation au graphe via une réduction gauche *)
  List.fold_left add_rel_to_graph g rels

(** 
 * remove_node_from_graph - Supprime un nœud et ses relations associées d'un graphe.
 *
 * @description 
 * Cette fonction supprime un nœud spécifié par son identifiant d'un graphe, ainsi que toutes les relations 
 * où ce nœud apparaît comme source ou cible.
 *
 * @param nid L'identifiant du nœud à supprimer, de type [string].
 * @param g Le graphe initial, de type [Graphstruct.db_graph].
 *
 * @return Retourne le graphe mis à jour, de type [Graphstruct.db_graph].
 *
 * @type [string -> Graphstruct.db_graph -> Graphstruct.db_graph]
 *
 * @var new_nodes Liste des nœuds après suppression, de type [Graphstruct.db_node list].
 * @var new_rels Liste des relations après suppression, de type [Graphstruct.db_rel list].
 *)
let remove_node_from_graph nid (DBG (nodes, rels)) =
  let new_nodes = List.filter (fun (DBN (n, _)) -> n <> nid) nodes in  (* Supprime le nœud *)
  let new_rels = List.filter (fun (DBR (s, _, t)) -> s <> nid && t <> nid) rels in  (* Supprime les relations associées *)
  DBG (new_nodes, new_rels)

(** 
 * remove_rels_from_graph - Supprime une liste de relations d'un graphe.
 *
 * @description 
 * Cette fonction supprime toutes les relations spécifiées d'un graphe, en conservant les nœuds inchangés.
 *
 * @param rels La liste des relations à supprimer, de type [Graphstruct.db_rel list].
 * @param g Le graphe initial, de type [Graphstruct.db_graph].
 *
 * @return Retourne le graphe mis à jour, de type [Graphstruct.db_graph].
 *
 * @type [Graphstruct.db_rel list -> Graphstruct.db_graph -> Graphstruct.db_graph]
 *
 * @var new_rels Liste des relations après suppression, de type [Graphstruct.db_rel list].
 *)
let remove_rels_from_graph rels (DBG (nodes, existing_rels)) =
  let new_rels = List.filter (fun r -> not (List.mem r rels)) existing_rels in  (* Supprime les relations spécifiées *)
  DBG (nodes, new_rels)

(** 
 * update_node_attrs - Met à jour un attribut d'un nœud dans un graphe.
 *
 * @description 
 * Cette fonction met à jour la valeur d'un attribut spécifique pour un nœud donné dans un graphe. Si 
 * l'attribut existe déjà, il est remplacé ; sinon, il est ajouté.
 *
 * @param nid L'identifiant du nœud à mettre à jour, de type [string].
 * @param fn Le nom de l'attribut à modifier, de type [string].
 * @param v La nouvelle valeur de l'attribut, de type [Lang.value].
 * @param g Le graphe initial, de type [Graphstruct.db_graph].
 *
 * @return Retourne le graphe mis à jour, de type [Graphstruct.db_graph].
 *
 * @type [string -> string -> Lang.value -> Graphstruct.db_graph -> Graphstruct.db_graph]
 *
 * @var new_nodes Liste des nœuds après mise à jour, de type [Graphstruct.db_node list].
 * @var new_attrs Liste des attributs mise à jour pour le nœud cible, de type [(string * Lang.value) list].
 *)
let update_node_attrs nid fn v (DBG (nodes, rels)) =
  let new_nodes = List.map (fun (DBN (n, (lbl, attrs))) ->
    if n = nid then
      let new_attrs = (fn, v) :: List.filter (fun (f, _) -> f <> fn) attrs in  (* Met à jour ou ajoute l'attribut *)
      DBN (n, (lbl, new_attrs))
    else DBN (n, (lbl, attrs))  (* Laisse les autres nœuds inchangés *)
  ) nodes in
  DBG (new_nodes, rels)


(** 
 * exec_instr - Exécute une instruction MiniGQL normalisée sur un état donné.
 *
 * @description 
 * Cette fonction exécute une instruction normalisée MiniGQL (création, correspondance, suppression, 
 * retour, filtrage ou mise à jour) en modifiant un état comprenant un graphe, une table et une mémoire 
 * de noms. Elle met à jour le graphe et/ou la table selon l'instruction, et lève une exception failwith 
 * en cas d'erreur (variable absente, types incorrects).
 *
 * @param s L'état initial, de type [Sem.state], sous la forme [State (g, tab, mn)] où g est le graphe, 
 *          tab la table et mn la mémoire de noms.
 * @param instr L'instruction à exécuter, de type [Instr.instruction].
 *
 * @return Retourne l'état mis à jour après exécution, de type [Sem.state].
 *
 * @type [Sem.state -> Instr.instruction -> Sem.state]
 *
 * @exception failwith Levée avec un message en cas de variable non trouvée dans la table, 
 *                     d'expression Where non booléenne, ou d'autres erreurs sémantiques.
 *
 * @var vns Liste des noms de variables dans la table, de type [string list].
 * @var lns Liste des lignes de la table (identifiants de nœuds), de type [string list list].
 * @var matching_nodes Liste des nœuds correspondant à une étiquette, de type [string list].
 * @var new_lns Nouvelle liste de lignes mise à jour, de type [string list list].
 * @var si Index de la variable source dans la table, de type [int].
 * @var ti Index de la variable cible dans la table, de type [int].
 * @var new_rels Liste des nouvelles relations à ajouter ou supprimer, de type [Graphstruct.db_rel list].
 * @var new_graph Graphe mis à jour après l'opération, de type [Graphstruct.db_graph].
 * @var nodes_to_remove Liste des nœuds à supprimer, de type [string list].
 * @var new_vns Nouvelle liste de variables après suppression, de type [string list].
 * @var indices Liste des indices des variables à retourner, de type [int list].
 * @var nodes_to_update Liste des nœuds à mettre à jour, de type [string list].
 * @var value Valeur évaluée pour une mise à jour d'attribut, de type [Lang.value].
 *)
let exec_instr (State (g, tab, mn) as s) = function
  | IActOnNode (CreateAct, v, lb) -> 
      (* Crée un nouveau nœud avec l'étiquette donnée *)
      create_node v lb s
  | IActOnNode (MatchAct, v, lb) ->
      let Table (vns, lns) = tab in
      let matching_nodes = get_nodes_by_label lb g in  (* Récupère les nœuds correspondant à lb *)
      let new_lns = List.concat_map (fun ln -> List.map (fun n -> n :: ln) matching_nodes) lns in  (* Ajoute chaque nœud aux lignes *)
      State (g, Table (v::vns, new_lns), mn)  (* Met à jour la table avec la nouvelle variable *)
  | IActOnRel (CreateAct, sv, lb, tv) ->
      let Table (vns, lns) = tab in
      (match find_index ((=) sv) vns, find_index ((=) tv) vns with
       | Some si, Some ti ->
           (* Crée une liste de relations à partir des lignes *)
           let new_rels = List.map (fun ln -> DBR (List.nth ln si, lb, List.nth ln ti)) lns in
           let new_graph = add_rels_to_graph new_rels g in  (* Ajoute les relations au graphe *)
           State (new_graph, tab, mn)
       | _ -> failwith "Variables not in table")  (* Variables absentes de la table *)
  | IActOnRel (MatchAct, sv, lb, tv) ->
      let Table (vns, lns) = tab in
      (match find_index ((=) sv) vns, find_index ((=) tv) vns with
       | Some si, Some ti ->
           let DBG (_, rels) = g in
           (* Filtre les lignes où la relation existe dans le graphe *)
           let valid_lns = List.filter (fun ln ->
             let s = List.nth ln si in
             let t = List.nth ln ti in
             List.exists (fun (DBR (src, rlbl, tgt)) -> src = s && rlbl = lb && tgt = t) rels
           ) lns in
           State (g, Table (vns, valid_lns), mn)  (* Met à jour la table avec les lignes valides *)
       | _ -> failwith "Variables not in table")
  | IDeleteNode v ->
      let Table (vns, lns) = tab in
      (match find_index ((=) v) vns with
       | Some i ->
           let nodes_to_remove = List.map (fun ln -> List.nth ln i) lns in  (* Liste des nœuds à supprimer *)
           let new_graph = List.fold_left (fun g nid -> remove_node_from_graph nid g) g nodes_to_remove in  (* Supprime chaque nœud *)
           let new_vns = List.filter ((<>) v) vns in  (* Supprime la variable de la table *)
           let new_lns = List.map (fun ln -> List.filteri (fun j _ -> j <> i) ln) lns in  (* Supprime la colonne correspondante *)
           State (new_graph, Table (new_vns, new_lns), mn)
       | None -> failwith "Variable not in table")
  | IDeleteRel (sv, lb, tv) ->
      let Table (vns, lns) = tab in
      (match find_index ((=) sv) vns, find_index ((=) tv) vns with
       | Some si, Some ti ->
           let rels_to_remove = List.map (fun ln -> DBR (List.nth ln si, lb, List.nth ln ti)) lns in  (* Liste des relations à supprimer *)
           let new_graph = remove_rels_from_graph rels_to_remove g in  (* Supprime les relations *)
           State (new_graph, tab, mn)
       | _ -> failwith "Variables not in table")
  | IReturn vs ->
      let Table (vns, lns) = tab in
      let indices = List.map (fun v ->
        match find_index ((=) v) vns with
        | Some i -> i
        | None -> failwith ("Variable " ^ v ^ " not in table")  (* Vérifie chaque variable *)
      ) vs in
      let new_lns = List.map (fun ln -> List.map (fun i -> List.nth ln i) indices) lns in  (* Projette les colonnes demandées *)
      State (g, Table (vs, new_lns), mn)  (* Met à jour la table avec les variables retournées *)
  | IWhere e ->
      let Table (vns, lns) = tab in
      let new_lns = List.filter (fun ln ->
        match eval_expr tab ln g e with
        | BoolV true -> true  (* Garde la ligne si la condition est vraie *)
        | BoolV false -> false
        | _ -> failwith "Where expression must evaluate to boolean"  (* Lève une erreur si non booléen *)
      ) lns in
      State (g, Table (vns, new_lns), mn)  (* Met à jour la table avec les lignes filtrées *)
  | ISet (vn, fn, e) ->
      let Table (vns, lns) = tab in
      (match find_index ((=) vn) vns with
       | Some i ->
           let nodes_to_update = List.map (fun ln -> List.nth ln i) lns in  (* Liste des nœuds à mettre à jour *)
           (* Évalue l’expression avec la première ligne pour simplifier *)
           let value = eval_expr tab (List.hd lns) g e in
           let new_graph = List.fold_left (fun g nid -> update_node_attrs nid fn value g) g nodes_to_update in  (* Met à jour les attributs *)
           State (new_graph, tab, mn)
       | None -> failwith ("Variable " ^ vn ^ " not in table"))

let exec (NormProg (_tps, NormQuery instrs)) = 
  List.fold_left exec_instr initial_state instrs