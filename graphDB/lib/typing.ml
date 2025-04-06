open Graphstruct
open Lang
open Instr
 
type environment = { types:  db_tp; bindings: (vname * label) list }
[@@deriving show]

let initial_environment gt = {types = gt; bindings = []}
let initial_result gt = Result.Ok (initial_environment gt)
  
exception FieldAccError of string
exception TypeError of string


type tc_result = (environment, string list) result

(* Functions for manipulating the environment *)

let add_var vn t (env:environment) = 
  {env with bindings = (vn,t)::env.bindings}

let remove_var vn env = 
  {env with bindings = List.remove_assoc vn env.bindings}

(* TODO: add more auxiliary functions here *)

(**
 * @name check_graph_types
 * @description Vérifie la validité d'un graphe de types (db_tp) en s'assurant qu'il n'y a pas de doublons dans les déclarations de nœuds ou de relations, et que toutes les relations référencent des nœuds déclarés.
 * @param DBG (ntdecls, rtdecls) : Un graphe de types composé de :
 *   - ntdecls : Liste de déclarations de nœuds (DBN (label, attrib_decl list)).
 *   - rtdecls : Liste de déclarations de relations (DBR (source, label, target)).
 * @return (unit, string) result :
 *   - Result.Ok () : Si le graphe est valide (aucune erreur).
 *   - Result.Error string : Une chaîne contenant les messages d'erreur concaténés avec "\n" si des problèmes sont détectés.
 * @vars
 *   - node_labels : Liste des étiquettes (labels) des nœuds extraites de ntdecls.
 *   - unique_node_labels : Liste des étiquettes uniques triées (sans doublons).
 *   - errors : Référence mutable pour accumuler les messages d'erreur.
 *   - valid_node_labels : Liste des étiquettes valides (identique à node_labels ici).
 *   - relation_triples : Liste des triplets (source, label, target) des relations.
 *   - unique_relation_triples : Liste des triplets uniques triés (sans doublons).
 *)
let check_graph_types (DBG (ntdecls, rtdecls)) : (unit, string) result =
  (* Extrait les étiquettes des nœuds de la liste ntdecls, ignore les attributs *)
  let node_labels = List.map (fun (DBN (lbl, _)) -> lbl) ntdecls in
  (* Trie et supprime les doublons dans les étiquettes pour détecter les répétitions *)
  let unique_node_labels = List.sort_uniq String.compare node_labels in
  (* Initialise une référence mutable pour stocker les erreurs au fur et à mesure *)
  let errors = ref [] in
  
  (* Vérifie s'il y a des doublons dans les déclarations de nœuds *)
  if List.length node_labels <> List.length unique_node_labels then
    (* Ajoute un message d'erreur si le nombre d'étiquettes diffère après suppression des doublons *)
    errors := "Multiple declarations of the same node type" :: !errors;
  
  (* Définit les étiquettes valides comme étant toutes celles déclarées (pas de filtrage ici) *)
  let valid_node_labels = node_labels in
  (* Définit une fonction auxiliaire pour vérifier chaque relation *)
  let check_relation (DBR (src, rlbl, tgt)) =
    (* Vérifie si la source de la relation est un nœud déclaré *)
    if not (List.mem src valid_node_labels) then
      (* Ajoute une erreur si la source n'est pas dans les nœuds valides *)
      errors := ("Reference to undeclared node type '" ^ src ^ "' in relation '" ^ rlbl ^ "'") :: !errors;
    (* Vérifie si la cible de la relation est un nœud déclaré *)
    if not (List.mem tgt valid_node_labels) then
      (* Ajoute une erreur si la cible n'est pas dans les nœuds valides *)
      errors := ("Reference to undeclared node type '" ^ tgt ^ "' in relation '" ^ rlbl ^ "'") :: !errors
  in
  (* Applique la vérification à toutes les relations dans rtdecls *)
  List.iter check_relation rtdecls;
  
  (* Transforme les relations en triplets pour faciliter la comparaison *)
  let relation_triples = List.map (fun (DBR (s, r, t)) -> (s, r, t)) rtdecls in
  (* Trie et supprime les doublons dans les triplets avec une fonction de comparaison personnalisée *)
  let unique_relation_triples = List.sort_uniq (fun (s1, r1, t1) (s2, r2, t2) ->
    let c1 = String.compare s1 s2 in  (* Compare d'abord les sources *)
    if c1 <> 0 then c1
    else let c2 = String.compare r1 r2 in  (* Puis les étiquettes si sources égales *)
    if c2 <> 0 then c2
    else String.compare t1 t2  (* Enfin les cibles si tout le reste est égal *)
  ) relation_triples in
  (* Vérifie s'il y a des doublons dans les déclarations de relations *)
  if List.length relation_triples <> List.length unique_relation_triples then
    (* Ajoute un message d'erreur si des relations identiques sont déclarées plusieurs fois *)
    errors := "Multiple declarations of the same relation type" :: !errors;
  
  (* Retourne le résultat final selon la présence ou non d'erreurs *)
  if !errors = [] then
    Result.Ok ()  (* Aucun problème détecté, graphe valide *)
  else
    (* Concatène les erreurs en une seule chaîne avec des sauts de ligne, inverse pour l'ordre chronologique *)
    Result.Error (String.concat "\n" (List.rev !errors))

(* TODO: fill in details *)
let rec tp_expr env = function
  Const v -> IntT
| AttribAcc (vn, fn) -> IntT
| BinOp (bop, e1, e2) -> tp_expr env e1

(* check expression e with expected type et in environment env *)
let check_expr e et env : tc_result = 
  try 
    if tp_expr env e = et
    then Result.Ok env
    else Result.Error ["Expression does not have expected type " ^ (show_attrib_tp et)]
  with 
  | TypeError s -> Result.Error [s]
  | FieldAccError s -> Result.Error [s]
  

  (**
 * @name tc_instr
 * @description Vérifie le typage d'une instruction individuelle dans un environnement donné, met à jour l'environnement si nécessaire, et renvoie un résultat indiquant la validité ou les erreurs.
 * @param i : instruction - Une instruction normalisée (ex. IActOnNode, IActOnRel) définie dans Instr.ml.
 * @param env : environment - L'environnement contenant le graphe de types (types) et les bindings (vname * label list).
 * @return tc_result : (environment, string list) result :
 *   - Result.Ok environment : Si l'instruction est valide, renvoie l'environnement mis à jour.
 *   - Result.Error string list : Liste des messages d'erreur si l'instruction est invalide.
 * @vars
 *   - node_exists : Fonction auxiliaire qui vérifie si un label de nœud existe dans env.types.
 *   - rel_exists : Fonction auxiliaire qui vérifie si une relation (src, rlbl, tgt) existe dans env.types.
 *   - lbl/lbl1/lbl2 : Étiquettes de nœuds associées à des variables dans les bindings.
 *   - new_env : Nouvel environnement mis à jour après certaines instructions (ex. ajout/suppression de variable).
 *   - unbound : Liste des variables non liées dans IReturn.
 *   - new_bindings : Bindings filtrés pour IReturn.
 *   - attribs : Liste des attributs associés à un nœud dans ISet.
 *   - expected_type : Type attendu pour l'expression dans ISet (défaut à BoolT si non trouvé).
 *   - et : Type attendu pour l'expression dans IWhere (toujours BoolT).
 *)
let tc_instr (i: instruction) (env: environment) : tc_result =
  (* Vérifie si un label de nœud existe dans le graphe de types *)
  let node_exists lbl = 
    List.exists (fun (DBN (l, _)) -> l = lbl) (nodes_of_graph env.types)
  in
  (* Vérifie si une relation (source, label, target) existe dans le graphe de types *)
  let rel_exists src rlbl tgt =
    List.exists (fun (DBR (s, r, t)) -> s = src && r = rlbl && t = tgt) (rels_of_graph env.types)
  in
  (* Analyse l'instruction selon son type *)
  match i with
  | IActOnNode (act, vn, lb) ->
      (* Vérifie si la variable est déjà liée dans l'environnement *)
      if List.mem_assoc vn env.bindings then
        Result.Error ["Variable '" ^ vn ^ "' is already bound"]  (* Erreur : variable déjà utilisée *)
      (* Vérifie si le label du nœud est déclaré dans le graphe de types *)
      else if not (node_exists lb) then
        Result.Error ["Node type '" ^ lb ^ "' is not declared"]  (* Erreur : type de nœud inconnu *)
      else
        (* Ajoute la variable avec son label à l'environnement *)
        let new_env = add_var vn lb env in
        Result.Ok new_env  (* Succès : renvoie l'environnement mis à jour *)
  | IActOnRel (act, vn1, rlbl, vn2) ->
      (* Récupère le label associé à vn1 dans les bindings, "" si non trouvé *)
      let lbl1 = try List.assoc vn1 env.bindings with Not_found -> "" in
      (* Récupère le label associé à vn2 dans les bindings, "" si non trouvé *)
      let lbl2 = try List.assoc vn2 env.bindings with Not_found -> "" in
      (* Vérifie si vn1 est liée *)
      if lbl1 = "" then
        Result.Error ["Variable '" ^ vn1 ^ "' is not bound"]  (* Erreur : vn1 non liée *)
      (* Vérifie si vn2 est liée *)
      else if lbl2 = "" then
        Result.Error ["Variable '" ^ vn2 ^ "' is not bound"]  (* Erreur : vn2 non liée *)
      (* Vérifie si la relation (lbl1, rlbl, lbl2) existe dans le graphe *)
      else if not (rel_exists lbl1 rlbl lbl2) then
        Result.Error ["Relation '" ^ rlbl ^ "' from '" ^ lbl1 ^ "' to '" ^ lbl2 ^ "' is not declared"]  (* Erreur : relation invalide *)
      else
        Result.Ok env  (* Succès : environnement inchangé *)
  | IDeleteNode vn ->
      (* Vérifie si la variable est liée dans l'environnement *)
      if not (List.mem_assoc vn env.bindings) then
        Result.Error ["Variable '" ^ vn ^ "' is not bound"]  (* Erreur : variable non liée *)
      else
        (* Supprime la variable de l'environnement *)
        let new_env = remove_var vn env in
        Result.Ok new_env  (* Succès : renvoie l'environnement mis à jour *)
  | IDeleteRel (vn1, rlbl, vn2) ->
      (* Récupère le label de vn1, "" si non trouvé *)
      let lbl1 = try List.assoc vn1 env.bindings with Not_found -> "" in
      (* Récupère le label de vn2, "" si non trouvé *)
      let lbl2 = try List.assoc vn2 env.bindings with Not_found -> "" in
      (* Vérifie si vn1 est liée *)
      if lbl1 = "" then
        Result.Error ["Variable '" ^ vn1 ^ "' is not bound"]  (* Erreur : vn1 non liée *)
      (* Vérifie si vn2 est liée *)
      else if lbl2 = "" then
        Result.Error ["Variable '" ^ vn2 ^ "' is not bound"]  (* Erreur : vn2 non liée *)
      (* Vérifie si la relation (lbl1, rlbl, lbl2) existe *)
      else if not (rel_exists lbl1 rlbl lbl2) then
        Result.Error ["Relation '" ^ rlbl ^ "' from '" ^ lbl1 ^ "' to '" ^ lbl2 ^ "' is not declared"]  (* Erreur : relation invalide *)
      else
        Result.Ok env  (* Succès : environnement inchangé *)
  | IReturn vns ->
      (* Identifie les variables non liées dans la liste vns *)
      let unbound = List.filter (fun vn -> not (List.mem_assoc vn env.bindings)) vns in
      (* Vérifie s'il y a des variables non liées *)
      if unbound <> [] then
        Result.Error (List.map (fun vn -> "Variable '" ^ vn ^ "' is not bound") unbound)  (* Erreur : variables non liées *)
      (* Vérifie s'il y a des doublons dans la liste des variables *)
      else if List.length vns <> List.length (List.sort_uniq String.compare vns) then
        Result.Error ["Return contains duplicate variables"]  (* Erreur : doublons détectés *)
      else
        (* Filtrer les bindings pour ne garder que ceux dans vns *)
        let new_bindings = List.filter (fun (vn, _) -> List.mem vn vns) env.bindings in
        Result.Ok { env with bindings = new_bindings }  (* Succès : renvoie l'environnement réduit *)
  | IWhere e ->
      (* Définit le type attendu de l'expression comme étant BoolT *)
      let et = BoolT in
      (* Vérifie le typage de l'expression *)
      begin match check_expr e et env with
      | Result.Ok _ -> Result.Ok env  (* Succès : expression booléenne valide, environnement inchangé *)
      | Result.Error errs -> Result.Error errs  (* Erreur : propage les erreurs de check_expr *)
      end
  | ISet (vn, fn, e) ->
      (* Récupère le label de vn, "" si non trouvé *)
      let lbl = try List.assoc vn env.bindings with Not_found -> "" in
      (* Vérifie si la variable est liée *)
      if lbl = "" then
        Result.Error ["Variable '" ^ vn ^ "' is not bound"]  (* Erreur : variable non liée *)
      else
        (* Récupère la liste des attributs du nœud associé à lbl *)
        let attribs = try List.assoc lbl (nodes_of_graph env.types |> List.map (fun (DBN (l, a)) -> (l, a)))
                      with Not_found -> [] in
        (* Récupère le type attendu de l'attribut fn, BoolT par défaut si non trouvé *)
        let expected_type = try List.assoc fn attribs with Not_found -> BoolT in
        (* Vérifie si l'expression correspond au type attendu *)
        begin match check_expr e expected_type env with
        | Result.Ok _ -> Result.Ok env  (* Succès : expression valide, environnement inchangé *)
        | Result.Error errs -> Result.Error errs  (* Erreur : propage les erreurs de check_expr *)
        end


(* type check list of instructions and stop on error *)
let check_and_stop (res : tc_result) i : tc_result = Result.bind res (tc_instr i)

let tc_instrs_stop gt instrs : tc_result = 
  List.fold_left check_and_stop (initial_result gt) instrs


  (* TODO: typecheck instructions *)
let typecheck_instructions continue gt instrs np = 
  let r = Result.Ok initial_environment in   (* call to real typechecker here *)
  match r with
  | Result.Error etc -> Printf.printf "%s\n" (String.concat "\n" etc); 
                        failwith "stopped"
  |_ -> np
  

  (* Typecheck program; 
     If continue is true, continue typechecking even 
     when errors have been discovered (can be ignored in a first version) *)  
let typecheck continue (NormProg(gt, NormQuery instrs) as np) = 
  match check_graph_types gt with
  | Result.Error egt -> Printf.printf "%s\n" ("Undeclared types in\n" ^ egt);
                        failwith "stopped"
  | _ -> typecheck_instructions continue gt instrs np
  