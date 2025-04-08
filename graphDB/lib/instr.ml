(* Normalized language, after removal of patterns and other syntactic sugar *)

open Lang

type action = CreateAct | MatchAct
  [@@deriving show]

type instruction =
  | IActOnNode of action * vname * label
  | IActOnRel of action * vname * label * vname
  | IDeleteNode of vname
  | IDeleteRel of vname * label * vname
  | IReturn of vname list
  | IWhere of expr
  | ISet of vname * fieldname * expr
  [@@deriving show]

type norm_query = NormQuery of instruction list
  [@@deriving show]

type norm_prog = NormProg of db_tp * norm_query
  [@@deriving show]

let normalize_node_pattern act = function 
  | DeclPattern (v, l) -> (v, [IActOnNode (act, v, l)])
  | VarRefPattern (v) -> (v, [])

(** 
 * normalize_pattern - Normalise un motif MiniGQL en une liste d'instructions.
 *
 * @description 
 * Cette fonction récursive transforme un motif du langage source MiniGQL (simple ou composé) en une 
 * séquence d'instructions normalisées. Elle gère deux cas : un motif simple (SimpPattern) qui est 
 * délégué à normalize_node_pattern, et un motif composé (CompPattern) qui combine un nœud avec une 
 * relation et un autre motif. Elle produit un tuple contenant la variable de départ et la liste des 
 * instructions générées, en respectant l'action spécifiée (par exemple, création ou correspondance).
 *
 * @param act L'action à appliquer au motif, de type [Instr.action] (CreateAct ou MatchAct).
 * @param pattern Le motif à normaliser, de type [Lang.pattern], qui peut être [SimpPattern] ou [CompPattern].
 *
 * @return Retourne un tuple de type [(Lang.vname * Instr.instruction list)] :
 *         - La première composante est la variable de départ du motif.
 *         - La seconde est la liste des instructions normalisées générées.
 *
 * @type [Instr.action -> Lang.pattern -> Lang.vname * Instr.instruction list]
 *
 * @var npt Patron de nœud initial dans un motif composé, de type [Lang.node_pattern].
 * @var rl Étiquette de la relation dans un motif composé, de type [Lang.label].
 * @var pt Sous-motif suivant dans un motif composé, de type [Lang.pattern].
 * @var v1 Variable associée au premier nœud normalisé, de type [Lang.vname].
 * @var ins1 Liste des instructions générées pour le premier nœud, de type [Instr.instruction list].
 * @var v2 Variable associée au sous-motif suivant, de type [Lang.vname].
 * @var ins2 Liste des instructions générées pour le sous-motif suivant, de type [Instr.instruction list].
 * @var firstInstr Première instruction de ins2, de type [Instr.instruction], utilisée pour gérer l'ordre.
 *)
let rec normalize_pattern act = function 
  | SimpPattern p -> 
      (* Délègue la normalisation d'un motif simple à normalize_node_pattern *)
      normalize_node_pattern act p
  | CompPattern (npt, rl, pt) -> 
      (* Normalise le premier nœud du motif composé *)
      let (v1, ins1) = normalize_node_pattern act npt in
      (* Normalise récursivement le sous-motif suivant *)
      let (v2, ins2) = normalize_pattern act pt in
      match ins2 with 
      | firstInstr::ins2 -> ( 
          match firstInstr with
          | IActOnNode _ -> 
              (* Si la première instruction est un nœud, insère la relation juste après *)
              (v1, ins1 @ firstInstr :: [IActOnRel(act, v1, rl, v2)] @ ins2 )
          | _ -> 
              (* Sinon, place la relation avant la première instruction *)
              (v1, ins1 @ [IActOnRel(act, v1, rl, v2)] @ firstInstr::ins2 ) 
          )
      | [] -> 
          (* Si pas de sous-instructions, ajoute simplement la relation *)
          (v1, ins1 @ [IActOnRel(act, v1, rl, v2)])


let normalize_clause = function
  | Create pats ->
      List.concat_map (fun p -> snd (normalize_pattern CreateAct p)) pats
  | Match pats ->
      List.concat_map (fun p -> snd (normalize_pattern MatchAct p)) pats
  | Delete (DeleteNodes vns) ->
      List.map (fun vn -> IDeleteNode vn) vns
  | Delete (DeleteRels rels) ->
      List.map (fun (vn1, rl, vn2) -> IDeleteRel (vn1, rl, vn2)) rels
  | Set sets ->
      List.map (fun (vn, fn, e) -> ISet (vn, fn, e)) sets
  | Where e ->
      [IWhere e]
  | Return vns ->
      [IReturn vns]

let normalize_query (Query cls) = NormQuery (List.concat_map normalize_clause cls)

let normalize_prog (Prog (tds, q)) = NormProg (tds, normalize_query q)