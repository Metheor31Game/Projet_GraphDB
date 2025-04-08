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

let check_graph_types (DBG (ntdecls, rtdecls)) : (unit, string) result =
  let node_labels = List.map (fun (DBN (lbl, _)) -> lbl) ntdecls in
  let unique_node_labels = List.sort_uniq String.compare node_labels in
  let errors = ref [] in
  
  if List.length node_labels <> List.length unique_node_labels then
    errors := "Multiple declarations of the same node type" :: !errors;
  
  let valid_node_labels = node_labels in
  let check_relation (DBR (src, rlbl, tgt)) =
    if not (List.mem src valid_node_labels) then
      errors := ("Reference to undeclared node type '" ^ src ^ "' in relation '" ^ rlbl ^ "'") :: !errors;
    if not (List.mem tgt valid_node_labels) then
      errors := ("Reference to undeclared node type '" ^ tgt ^ "' in relation '" ^ rlbl ^ "'") :: !errors
  in
  List.iter check_relation rtdecls;
  
  let relation_triples = List.map (fun (DBR (s, r, t)) -> (s, r, t)) rtdecls in
  let unique_relation_triples = List.sort_uniq (fun (s1, r1, t1) (s2, r2, t2) ->
    let c1 = String.compare s1 s2 in
    if c1 <> 0 then c1
    else let c2 = String.compare r1 r2 in
    if c2 <> 0 then c2
    else String.compare t1 t2
  ) relation_triples in
  if List.length relation_triples <> List.length unique_relation_triples then
    errors := "Multiple declarations of the same relation type" :: !errors;
  
  if !errors = [] then Result.Ok () else Result.Error (String.concat "\n" (List.rev !errors))

let rec tp_expr env = function
  | Const v -> (
      match v with
      | BoolV _ -> BoolT
      | IntV _ -> IntT
      | StringV _ -> StringT)
  | AttribAcc (vn, fn) -> (
      match List.assoc_opt vn env.bindings with
      | Some lbl ->
          let attribs = List.assoc lbl (List.map (fun (DBN (l, a)) -> (l, a)) (nodes_of_graph env.types)) in
          List.assoc fn attribs
      | None -> raise (TypeError ("Variable '" ^ vn ^ "' not bound")))
  | BinOp (bop, e1, e2) ->
      let t1 = tp_expr env e1 in
      let t2 = tp_expr env e2 in
      match bop with
      | BArith _ -> if t1 = IntT && t2 = IntT then IntT else raise (TypeError "Arithmetic operation requires int types")
      | BCompar _ -> if t1 = t2 then BoolT else raise (TypeError "Comparison requires same types")
      | BLogic _ -> if t1 = BoolT && t2 = BoolT then BoolT else raise (TypeError "Logic operation requires bool types")

let check_expr e et env : tc_result = 
  try 
    if tp_expr env e = et then Result.Ok env
    else Result.Error ["Expression does not have expected type " ^ (show_attrib_tp et)]
  with 
  | TypeError s -> Result.Error [s]
  | FieldAccError s -> Result.Error [s]

  let tc_instr (i: instruction) (env: environment) : environment =
    let node_exists lbl = 
      List.exists (fun (DBN (l, _)) -> l = lbl) (nodes_of_graph env.types)
    in
    let rel_exists src rlbl tgt =
      List.exists (fun (DBR (s, r, t)) -> s = src && r = rlbl && t = tgt) (rels_of_graph env.types)
    in
    match i with
    | IActOnNode (_, vn, lb) ->
        if not (node_exists lb) then
          raise (TypeCheckError ["Node type '" ^ lb ^ "' is not declared"])
        else
          add_var vn lb env  (* Permet la réutilisation de variables *)
    | IActOnRel (act, vn1, rlbl, vn2) ->
        let lbl1 = try List.assoc vn1 env.bindings with Not_found -> raise (TypeCheckError ["Variable '" ^ vn1 ^ "' is not bound"]) in
        let lbl2 = try List.assoc vn2 env.bindings with Not_found -> raise (TypeCheckError ["Variable '" ^ vn2 ^ "' is not bound"]) in
        if not (rel_exists lbl1 rlbl lbl2) then
          raise (TypeCheckError ["Relation '" ^ rlbl ^ "' from '" ^ lbl1 ^ "' to '" ^ lbl2 ^ "' is not declared"])
        else
          env
    | IDeleteNode vn ->
        if not (List.mem_assoc vn env.bindings) then
          raise (TypeCheckError ["Variable '" ^ vn ^ "' is not bound"])
        else
          remove_var vn env
    | IDeleteRel (vn1, rlbl, vn2) ->
        let lbl1 = try List.assoc vn1 env.bindings with Not_found -> raise (TypeCheckError ["Variable '" ^ vn1 ^ "' is not bound"]) in
        let lbl2 = try List.assoc vn2 env.bindings with Not_found -> raise (TypeCheckError ["Variable '" ^ vn2 ^ "' is not bound"]) in
        if not (rel_exists lbl1 rlbl lbl2) then
          raise (TypeCheckError ["Relation '" ^ rlbl ^ "' from '" ^ lbl1 ^ "' to '" ^ lbl2 ^ "' is not declared"])
        else
          env
    | IReturn vns ->
        let unbound = List.filter (fun vn -> not (List.mem_assoc vn env.bindings)) vns in
        if unbound <> [] then
          raise (TypeCheckError (List.map (fun vn -> "Variable '" ^ vn ^ "' is not bound") unbound))
        else if List.length vns <> List.length (List.sort_uniq String.compare vns) then
          raise (TypeCheckError ["Return contains duplicate variables"])
        else
          { env with bindings = List.filter (fun (vn, _) -> List.mem vn vns) env.bindings }
    | IWhere e ->
        let et = BoolT in
        (match check_expr e et env with
         | Result.Ok _ -> env
         | Result.Error errs -> raise (TypeCheckError errs))
    | ISet (vn, fn, e) ->
        let lbl = try List.assoc vn env.bindings with Not_found -> raise (TypeCheckError ["Variable '" ^ vn ^ "' is not bound"]) in
        let attribs = try List.assoc lbl (nodes_of_graph env.types |> List.map (fun (DBN (l, a)) -> (l, a)))
                      with Not_found -> [] in
        let expected_type = try List.assoc fn attribs with Not_found -> raise (TypeCheckError ["Attribute '" ^ fn ^ "' not declared for node type '" ^ lbl ^ "'"]) in
        (match check_expr e expected_type env with
         | Result.Ok _ -> env
         | Result.Error errs -> raise (TypeCheckError errs))

let tc_instrs_stop instrs env =
  List.fold_left (fun env i -> tc_instr i env) env instrs

let typecheck _continue (NormProg (gt, NormQuery instrs) as np) : Instr.norm_prog =
  match check_graph_types gt with
  | Result.Error egt -> raise (TypeCheckError ["Undeclared types in graph:\n" ^ egt])
  | Result.Ok () ->
      let env = initial_environment gt in
      let _ = tc_instrs_stop instrs env in
      np