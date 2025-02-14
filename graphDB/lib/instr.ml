(* Normalized language, after removal of patterns and other syntactic sugar *)

open Lang

type action = CreateAct | MatchAct
  [@@deriving show]

type instruction
  = IActOnNode of action * vname * label
  | IActOnRel of action * vname * label * vname
  | IDeleteNode of vname
  | IDeleteRel of vname * label * vname 
  | IReturn of vname list
  | IWhere of expr
  | ISet of vname * fieldname * expr 
  [@@deriving show]

(* Normalized query *)
type norm_query = NormQuery of instruction list
  [@@deriving show]

type norm_prog = NormProg of db_tp * norm_query
  [@@deriving show]


let normalize_node_pattern act = function 
| DeclPattern (v, l) -> (v, [IActOnNode(act, v, l)])
| VarRefPattern (v) -> (v, [])


let rec normalize_pattern act = function 
| SimpPattern p -> normalize_node_pattern act p
| CompPattern (npt, rl, pt) -> failwith "not yet implemented"

let normalize_clause = function
  | Create pats -> 
    List.concat_map (fun  p -> snd (normalize_pattern CreateAct p)) pats
  | _ -> []

let normalize_query (Query cls) = NormQuery (List.concat_map normalize_clause cls)

let normalize_prog (Prog(tds, q)) = NormProg(tds, normalize_query q)
