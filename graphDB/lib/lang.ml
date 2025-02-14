
  (* Names and labels *)
type vname = string   (* names for variables ... *)
  [@@deriving show]
type fieldname = string   (* names for attribute fields *)
  [@@deriving show]
type label = string  (* labels serving as names for node or relation types *)
  [@@deriving show]

  (* binary arithmetic operators: +, -, *, /, mod *)
type barith = BAadd | BAsub | BAmul | BAdiv | BAmod
  [@@deriving show]
  
  (* binary comparison operators: =, >=, >, <=, <, != *)
type bcompar = BCeq | BCge | BCgt | BCle | BClt | BCne
  [@@deriving show]

  (* binary logic operators *)
type blogic = BLand | BLor
  [@@deriving show]

  (* binary operators, combining all of the above *)
type binop
    = BArith of barith
    | BCompar of bcompar
    | BLogic of blogic
  [@@deriving show]

type value
    = BoolV of bool
    | IntV of int
    | StringV of string
  [@@deriving show]

let is_true = function
| BoolV true -> true
| _ -> false
  
  (* expresssions *)
type expr
    = Const of value                     (* constant *)
    | AttribAcc of vname * fieldname     (* attribute access *)
    | BinOp of binop * expr * expr       (* binary operation *)
  [@@deriving show]

  (* TODO: needs to be extended to deal with attributes *)
type node_pattern 
  = DeclPattern of vname * label    (* full node pattern with type declaration *)
  | VarRefPattern of vname          (* simple reference to var representing a node *)
  [@@deriving show]

type pattern 
  = SimpPattern of node_pattern
  | CompPattern of node_pattern * label * pattern
  [@@deriving show]

type delete_pattern
  = DeleteNodes of vname list
  | DeleteRels of (vname * label * vname) list
  [@@deriving show]

type clause 
  = Create of pattern list
  | Match of pattern list
  | Delete of delete_pattern
  | Return of vname list
  | Where of expr 
  | Set of (vname * fieldname * expr) list
  [@@deriving show]

type query = Query of clause list
  [@@deriving show]

(* Types *)
type attrib_tp = BoolT | IntT | StringT
  [@@deriving show]

type attrib_decl = fieldname * attrib_tp  
  [@@deriving show]

type db_tp = (label, attrib_decl list, label) Graphstruct.db_graph
[@@deriving show]
type prog = Prog of db_tp * query
  [@@deriving show]

