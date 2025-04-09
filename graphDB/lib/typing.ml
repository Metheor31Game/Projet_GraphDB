open Graphstruct
open Lang
open Instr
 
type environment = { types: db_tp; bindings: (vname * label) list }
[@@deriving show]

let initial_environment gt = { types = gt; bindings = [] }
let initial_result gt = Result.Ok (initial_environment gt)
  
exception FieldAccError of string
exception TypeError of string
exception TypeCheckError of string list

type tc_result = (environment, string list) result

(* Functions for manipulating the environment *)

let add_var vn t (env: environment) = 
  { env with bindings = (vn, t) :: env.bindings }

let remove_var vn env = 
  { env with bindings = List.remove_assoc vn env.bindings }

(** 
 * Vérifie la cohérence des déclarations de types dans un graphe de types MiniGQL.
 *
 * @description 
 * Cette fonction analyse les déclarations de nœuds et de relations d'un graphe de types pour détecter 
 * les éventuelles incohérences : doublons dans les types de nœuds ou de relations, et références à des 
 * types de nœuds non déclarés dans les relations. Elle accumule les erreurs dans une liste mutable et 
 * retourne un résultat indiquant soit un succès (aucune erreur), soit une erreur avec un message 
 * concaténé des problèmes rencontrés.
 *
 * @param graph Le graphe de types à vérifier, de type [(label, attrib_decl list, label) Graphstruct.db_graph].
 *             Déstructuré en DBG (ntdecls, rtdecls), où ntdecls est la liste des déclarations de nœuds 
 *             et rtdecls celle des relations.
 *
 * @return Retourne un résultat de type [(unit, string) result] :
 *         - [Result.Ok ()] si aucune erreur n'est détectée.
 *         - [Result.Error msg] si des erreurs sont trouvées, où [msg] est une chaîne de caractères 
 *           contenant les messages d'erreur séparés par des sauts de ligne.
 *
 * @type [(label, attrib_decl list, label) Graphstruct.db_graph -> (unit, string) result]
 *
 * @var node_labels Liste des étiquettes des nœuds extraites des déclarations, de type [string list].
 * @var unique_node_labels Liste triée et sans doublons des étiquettes de nœuds, de type [string list].
 * @var errors Référence mutable contenant la liste des messages d'erreur, de type [string list ref].
 * @var valid_node_labels Alias pour [node_labels], utilisé pour vérifier les relations, de type [string list].
 * @var check_relation Fonction auxiliaire vérifiant une relation individuelle, de type 
 *                     [(label * label * label) -> unit].
 * @var relation_triples Liste des triplets (source, relation, cible) des relations, de type 
 *                       [(string * string * string) list].
 * @var unique_relation_triples Liste triée et sans doublons des triplets de relations, de type 
 *                              [(string * string * string) list].
 *)
let check_graph_types (DBG (ntdecls, rtdecls)) : (unit, string) result =
  (* Extraction des étiquettes des nœuds à partir des déclarations *)
  let node_labels = List.map (fun (DBN (lbl, _)) -> lbl) ntdecls in
  (* Tri et suppression des doublons pour détecter les déclarations multiples *)
  let unique_node_labels = List.sort_uniq String.compare node_labels in
  (* Initialisation d'une référence mutable pour accumuler les erreurs *)
  let errors = ref [] in
  
  (* Vérification des doublons dans les types de nœuds *)
  if List.length node_labels <> List.length unique_node_labels then
    errors := "Multiple declarations of the same node type" :: !errors;
  
  (* Alias pour les étiquettes valides, utilisé dans la vérification des relations *)
  let valid_node_labels = node_labels in
  (* Définition de la fonction auxiliaire pour vérifier une relation *)
  let check_relation (DBR (src, rlbl, tgt)) =
    (* Vérifie si le nœud source est déclaré *)
    if not (List.mem src valid_node_labels) then
      errors := ("Reference to undeclared node type '" ^ src ^ "' in relation '" ^ rlbl ^ "'") :: !errors;
    (* Vérifie si le nœud cible est déclaré *)
    if not (List.mem tgt valid_node_labels) then
      errors := ("Reference to undeclared node type '" ^ tgt ^ "' in relation '" ^ rlbl ^ "'") :: !errors
  in
  (* Application de la vérification à toutes les relations *)
  List.iter check_relation rtdecls;
  
  (* Extraction des triplets (source, relation, cible) des relations *)
  let relation_triples = List.map (fun (DBR (s, r, t)) -> (s, r, t)) rtdecls in
  (* Tri et suppression des doublons pour détecter les déclarations multiples de relations *)
  let unique_relation_triples = List.sort_uniq (fun (s1, r1, t1) (s2, r2, t2) ->
    let c1 = String.compare s1 s2 in
    if c1 <> 0 then c1 (* Comparaison des sources *)
    else let c2 = String.compare r1 r2 in
      if c2 <> 0 then c2 (* Comparaison des étiquettes de relation *)
      else String.compare t1 t2 (* Comparaison des cibles *)
  ) relation_triples in
  (* Vérification des doublons dans les types de relations *)
  if List.length relation_triples <> List.length unique_relation_triples then
    errors := "Multiple declarations of the same relation type" :: !errors;
  
  (* Retourne Ok si aucune erreur, sinon Error avec les messages concaténés *)
  if !errors = [] then Result.Ok () else Result.Error (String.concat "\n" (List.rev !errors))

(** 
 * tp_expr - Détermine le type d'une expression dans le langage MiniGQL.
 *
 * @description 
 * Cette fonction récursive calcule le type d'une expression donnée en fonction d'un environnement de typage. 
 * Elle gère trois cas : les constantes (booléennes, entières, chaînes), les accès aux attributs des nœuds, 
 * et les opérations binaires (arithmétiques, comparatives, logiques). En cas d'erreur de typage ou de 
 * variable non liée, une exception de type TypeError est levée avec un message approprié.
 *
 * @param env L'environnement de typage, de type [environment], contenant les types des nœuds et les 
 *            bindings des variables.
 * @param expr L'expression à typer, de type [Lang.expr], qui peut être une constante, un accès à un 
 *             attribut ou une opération binaire.
 *
 * @return Retourne le type de l'expression, de type [Lang.attrib_tp], qui peut être [BoolT], [IntT] ou 
 *         [StringT].
 *
 * @type [environment -> Lang.expr -> Lang.attrib_tp]
 *
 * @exception TypeError Levée avec un message si une variable n'est pas liée ou si les types des 
 *                      opérandes d'une opération binaire sont incompatibles.
 *
 * @var v Valeur extraite d'une constante, de type [Lang.value], utilisée pour déterminer son type.
 * @var lbl Étiquette d'un nœud associée à une variable, de type [string], extraite des bindings.
 * @var attribs Liste des attributs associés à une étiquette de nœud, de type [(string * Lang.attrib_tp) list].
 * @var t1 Type de la première sous-expression d'une opération binaire, de type [Lang.attrib_tp].
 * @var t2 Type de la seconde sous-expression d'une opération binaire, de type [Lang.attrib_tp].
 *)
let rec tp_expr env = function
  (* Cas des constantes *)
  | Const v -> (
      match v with
      | BoolV _ -> BoolT  (* Une constante booléenne est de type BoolT *)
      | IntV _ -> IntT    (* Une constante entière est de type IntT *)
      | StringV _ -> StringT)  (* Une constante chaîne est de type StringT *)
  (* Cas des accès aux attributs *)
  | AttribAcc (vn, fn) -> (
      match List.assoc_opt vn env.bindings with
      | Some lbl ->
          (* Récupération des attributs associés à l'étiquette du nœud *)
          let attribs = List.assoc lbl (List.map (fun (DBN (l, a)) -> (l, a)) (nodes_of_graph env.types)) in
          (* Retourne le type de l'attribut spécifié *)
          List.assoc fn attribs
      | None -> 
          (* Lève une exception si la variable n'est pas liée dans l'environnement *)
          raise (TypeError ("Variable '" ^ vn ^ "' not bound")))
  (* Cas des opérations binaires *)
  | BinOp (bop, e1, e2) ->
      (* Calcul récursif des types des sous-expressions *)
      let t1 = tp_expr env e1 in
      let t2 = tp_expr env e2 in
      match bop with
      | BArith _ -> 
          (* Vérifie que les deux opérandes sont des entiers pour une opération arithmétique *)
          if t1 = IntT && t2 = IntT then IntT 
          else raise (TypeError "Arithmetic operation requires int types")
      | BCompar _ -> 
          (* Vérifie que les deux opérandes sont du même type pour une comparaison *)
          if t1 = t2 then BoolT 
          else raise (TypeError "Comparison requires same types")
      | BLogic _ -> 
          (* Vérifie que les deux opérandes sont booléens pour une opération logique *)
          if t1 = BoolT && t2 = BoolT then BoolT 
          else raise (TypeError "Logic operation requires bool types")

let check_expr e et env : tc_result = 
  try 
    if tp_expr env e = et then Result.Ok env
    else Result.Error ["Expression does not have expected type " ^ (show_attrib_tp et)]
  with 
  | TypeError s -> Result.Error [s]
  | FieldAccError s -> Result.Error [s]

(** 
 * tc_instr - Vérifie le typage d'une instruction MiniGQL et met à jour l'environnement.
 *
 * @description 
 * Cette fonction vérifie la cohérence de typage d'une instruction dans le langage MiniGQL normalisé 
 * (par exemple, création de nœuds, relations, suppressions, etc.) en fonction d'un environnement donné. 
 * Elle met à jour l'environnement en ajoutant ou supprimant des variables si nécessaire, et lève une 
 * exception TypeCheckError en cas d'erreur de typage (types non déclarés, variables non liées, etc.).
 *
 * @param i L'instruction à vérifier, de type [Instr.instruction].
 * @param env L'environnement de typage initial, de type [environment].
 *
 * @return Retourne l'environnement mis à jour après l'instruction, de type [environment].
 *
 * @type [Instr.instruction -> environment -> environment]
 *
 * @exception TypeCheckError Levée avec une liste de messages si une erreur de typage est détectée.
 *
 * @var node_exists Fonction auxiliaire vérifiant l'existence d'un type de nœud, de type [string -> bool].
 * @var rel_exists Fonction auxiliaire vérifiant l'existence d'une relation, de type [string -> string -> string -> bool].
 * @var lbl1 Étiquette du premier nœud dans une relation, de type [string].
 * @var lbl2 Étiquette du second nœud dans une relation, de type [string].
 * @var unbound Liste des variables non liées dans une instruction Return, de type [string list].
 * @var lbl Étiquette d'un nœud associée à une variable, de type [string].
 * @var attribs Liste des attributs d'un type de nœud, de type [(string * Lang.attrib_tp) list].
 * @var expected_type Type attendu d'une expression dans une affectation, de type [Lang.attrib_tp].
 * @var et Type attendu d'une expression Where (toujours BoolT), de type [Lang.attrib_tp].
 *)
let tc_instr (i: instruction) (env: environment) : environment =
  (* Vérifie si un type de nœud existe dans le graphe de types *)
  let node_exists lbl = 
    List.exists (fun (DBN (l, _)) -> l = lbl) (nodes_of_graph env.types)
  in
  (* Vérifie si une relation existe entre deux types de nœuds *)
  let rel_exists src rlbl tgt =
    List.exists (fun (DBR (s, r, t)) -> s = src && r = rlbl && t = tgt) (rels_of_graph env.types)
  in
  match i with
  | IActOnNode (_, vn, lb) ->
      (* Vérifie si le type de nœud est déclaré *)
      if not (node_exists lb) then
        raise (TypeCheckError ["Node type '" ^ lb ^ "' is not declared"])
      else
        add_var vn lb env  (* Ajoute la variable à l'environnement, permet la réutilisation *)
  | IActOnRel (act, vn1, rlbl, vn2) ->
      (* Récupère le type du premier nœud ou lève une erreur si non lié *)
      let lbl1 = try List.assoc vn1 env.bindings with Not_found -> 
        raise (TypeCheckError ["Variable '" ^ vn1 ^ "' is not bound"]) in
      (* Récupère le type du second nœud ou lève une erreur si non lié *)
      let lbl2 = try List.assoc vn2 env.bindings with Not_found -> 
        raise (TypeCheckError ["Variable '" ^ vn2 ^ "' is not bound"]) in
      (* Vérifie si la relation est déclarée *)
      if not (rel_exists lbl1 rlbl lbl2) then
        raise (TypeCheckError ["Relation '" ^ rlbl ^ "' from '" ^ lbl1 ^ "' to '" ^ lbl2 ^ "' is not declared"])
      else
        env  (* Pas de modification de l'environnement *)
  | IDeleteNode vn ->
      (* Vérifie si la variable est liée avant suppression *)
      if not (List.mem_assoc vn env.bindings) then
        raise (TypeCheckError ["Variable '" ^ vn ^ "' is not bound"])
      else
        remove_var vn env  (* Supprime la variable de l'environnement *)
  | IDeleteRel (vn1, rlbl, vn2) ->
      let lbl1 = try List.assoc vn1 env.bindings with Not_found -> 
        raise (TypeCheckError ["Variable '" ^ vn1 ^ "' is not bound"]) in
      let lbl2 = try List.assoc vn2 env.bindings with Not_found -> 
        raise (TypeCheckError ["Variable '" ^ vn2 ^ "' is not bound"]) in
      if not (rel_exists lbl1 rlbl lbl2) then
        raise (TypeCheckError ["Relation '" ^ rlbl ^ "' from '" ^ lbl1 ^ "' to '" ^ lbl2 ^ "' is not declared"])
      else
        env
  | IReturn vns ->
      (* Identifie les variables non liées *)
      let unbound = List.filter (fun vn -> not (List.mem_assoc vn env.bindings)) vns in
      if unbound <> [] then
        raise (TypeCheckError (List.map (fun vn -> "Variable '" ^ vn ^ "' is not bound") unbound))
      else if List.length vns <> List.length (List.sort_uniq String.compare vns) then
        raise (TypeCheckError ["Return contains duplicate variables"])  (* Vérifie les doublons *)
      else
        { env with bindings = List.filter (fun (vn, _) -> List.mem vn vns) env.bindings }  (* Filtre les bindings *)
  | IWhere e ->
      let et = BoolT in  (* Type attendu pour une condition Where *)
      (match check_expr e et env with
        | Result.Ok _ -> env  (* Pas de modification si l'expression est valide *)
        | Result.Error errs -> raise (TypeCheckError errs))  (* Lève les erreurs de typage *)
  | ISet (vn, fn, e) ->
      let lbl = try List.assoc vn env.bindings with Not_found -> 
        raise (TypeCheckError ["Variable '" ^ vn ^ "' is not bound"]) in
      (* Récupère les attributs du type de nœud *)
      let attribs = try List.assoc lbl (nodes_of_graph env.types |> List.map (fun (DBN (l, a)) -> (l, a)))
                    with Not_found -> [] in
      let expected_type = try List.assoc fn attribs with Not_found -> 
        raise (TypeCheckError ["Attribute '" ^ fn ^ "' not declared for node type '" ^ lbl ^ "'"]) in
      (match check_expr e expected_type env with
        | Result.Ok _ -> env  (* Pas de modification si l'affectation est valide *)
        | Result.Error errs -> raise (TypeCheckError errs))  (* Lève les erreurs de typage *)

let tc_instrs_stop instrs env =
  List.fold_left (fun env i -> tc_instr i env) env instrs

(** 
 * typecheck - Vérifie le typage complet d'un programme MiniGQL normalisé.
 *
 * @description 
 * Cette fonction vérifie la cohérence de typage d'un programme normalisé MiniGQL, en deux étapes : 
 * d'abord la validation du graphe de types avec check_graph_types, puis la vérification des instructions 
 * avec tc_instrs_stop. Si aucune erreur n'est détectée, elle retourne le programme inchangé ; sinon, 
 * elle lève une exception TypeCheckError avec les messages d'erreur appropriés.
 *
 * @param _continue Paramètre ignoré (pour compatibilité), de type [bool].
 * @param np Le programme normalisé à vérifier, de type [Instr.norm_prog], sous la forme [NormProg (gt, NormQuery instrs)].
 *
 * @return Retourne le programme normalisé inchangé si valide, de type [Instr.norm_prog].
 *
 * @type [bool -> Instr.norm_prog -> Instr.norm_prog]
 *
 * @exception TypeCheckError Levée avec une liste de messages si une erreur est détectée dans le graphe 
 *                           de types ou les instructions.
 *
 * @var env Environnement initial construit à partir du graphe de types, de type [environment].
 *)
let typecheck _continue (NormProg (gt, NormQuery instrs) as np) : Instr.norm_prog =
  match check_graph_types gt with
  | Result.Error egt -> 
      (* Lève une erreur si le graphe de types est invalide *)
      let rec printerrors str i =
        (* i est l'indice du caractère courant dans la chaîne *)
        if i >= String.length str then
          ()  (* Fin de la chaîne, on arrête *)
        else
          let current_char = str.[i] in
          if current_char = '\n' then
            begin
              Printf.printf "%s\n" (String.sub str 0 i);  (* Affiche ce qui a été accumulé jusqu'au '\n' *)
              printerrors str (i + 1)  (* Passe au caractère suivant *)
            end
          else
            printerrors str (i + 1)  (* Continue sans afficher si ce n'est pas un '\n' *)
      in
      printerrors egt 0;  (* On commence à parcourir la chaîne depuis le début *)
      raise (TypeCheckError ["Undeclared types in graph:\n" ^ egt])
  | Result.Ok () ->
      (* Initialise l'environnement avec le graphe de types *)
      let env = initial_environment gt in
      (* Vérifie toutes les instructions et ignore le résultat intermédiaire *)
      let _ = tc_instrs_stop instrs env in
      np  (* Retourne le programme inchangé si tout est valide *)