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

let rec normalize_pattern act = function 
  | SimpPattern p -> normalize_node_pattern act p
  | CompPattern (npt, rl, pt) ->
      let (vn1, instrs1) = normalize_node_pattern act npt in
      let (vn2, instrs2) = normalize_pattern act pt in
      (vn1, instrs1 @ [IActOnRel (act, vn1, rl, vn2)] @ instrs2)

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