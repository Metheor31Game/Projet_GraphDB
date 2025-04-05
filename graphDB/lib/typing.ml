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

(* TODO: fill in details *)
let check_graph_types (DBG (ntdecls, rtdecls)) : (unit, string) result =
  let node_labels = List.map (fun (DBN (lbl, _)) -> lbl) ntdecls in
  let unique_node_labels = List.sort_uniq String.compare node_labels in
  let errors = ref [] in  (* Utiliser une référence pour accumuler les erreurs *)
  
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
  
  if !errors = [] then
    Result.Ok ()
  else
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
  

let tc_instr (i: instruction) (env: environment) : tc_result =
  let node_exists lbl = 
    List.exists (fun (DBN (l, _)) -> l = lbl) (nodes_of_graph env.types)
  in
  let rel_exists src rlbl tgt =
    List.exists (fun (DBR (s, r, t)) -> s = src && r = rlbl && t = tgt) (rels_of_graph env.types)
  in
  match i with
  | IActOnNode (act, vn, lb) ->
      (* Vérifier que la variable n'est pas déjà liée et que le label existe *)
      if List.mem_assoc vn env.bindings then
        Result.Error ["Variable '" ^ vn ^ "' is already bound"]
      else if not (node_exists lb) then
        Result.Error ["Node type '" ^ lb ^ "' is not declared"]
      else
        let new_env = add_var vn lb env in
        Result.Ok new_env
  | IActOnRel (act, vn1, rlbl, vn2) ->
      (* Vérifier que les variables existent et que la relation est valide *)
      let lbl1 = try List.assoc vn1 env.bindings with Not_found -> "" in
      let lbl2 = try List.assoc vn2 env.bindings with Not_found -> "" in
      if lbl1 = "" then
        Result.Error ["Variable '" ^ vn1 ^ "' is not bound"]
      else if lbl2 = "" then
        Result.Error ["Variable '" ^ vn2 ^ "' is not bound"]
      else if not (rel_exists lbl1 rlbl lbl2) then
        Result.Error ["Relation '" ^ rlbl ^ "' from '" ^ lbl1 ^ "' to '" ^ lbl2 ^ "' is not declared"]
      else
        Result.Ok env  (* L'environnement ne change pas *)
  | IDeleteNode vn ->
      (* Vérifier que la variable est déclarée, puis la supprimer *)
      if not (List.mem_assoc vn env.bindings) then
        Result.Error ["Variable '" ^ vn ^ "' is not bound"]
      else
        let new_env = remove_var vn env in
        Result.Ok new_env
  | IDeleteRel (vn1, rlbl, vn2) ->
      (* Vérifier que les variables existent et que la relation est valide *)
      let lbl1 = try List.assoc vn1 env.bindings with Not_found -> "" in
      let lbl2 = try List.assoc vn2 env.bindings with Not_found -> "" in
      if lbl1 = "" then
        Result.Error ["Variable '" ^ vn1 ^ "' is not bound"]
      else if lbl2 = "" then
        Result.Error ["Variable '" ^ vn2 ^ "' is not bound"]
      else if not (rel_exists lbl1 rlbl lbl2) then
        Result.Error ["Relation '" ^ rlbl ^ "' from '" ^ lbl1 ^ "' to '" ^ lbl2 ^ "' is not declared"]
      else
        Result.Ok env  (* L'environnement ne change pas *)
  | IReturn vns ->
      (* Vérifier que toutes les variables sont liées et distinctes *)
      let unbound = List.filter (fun vn -> not (List.mem_assoc vn env.bindings)) vns in
      if unbound <> [] then
        Result.Error (List.map (fun vn -> "Variable '" ^ vn ^ "' is not bound") unbound)
      else if List.length vns <> List.length (List.sort_uniq String.compare vns) then
        Result.Error ["Return contains duplicate variables"]
      else
        let new_bindings = List.filter (fun (vn, _) -> List.mem vn vns) env.bindings in
        Result.Ok { env with bindings = new_bindings }
  | IWhere e ->
      (* Vérifier que l'expression est booléenne *)
      let et = BoolT in  (* Type attendu *)
      begin match check_expr e et env with
      | Result.Ok _ -> Result.Ok env  (* L'environnement ne change pas *)
      | Result.Error errs -> Result.Error errs
      end
  | ISet (vn, fn, e) ->
      (* Vérifier que la variable existe et que l'expression correspond au type de l'attribut *)
      let lbl = try List.assoc vn env.bindings with Not_found -> "" in
      if lbl = "" then
        Result.Error ["Variable '" ^ vn ^ "' is not bound"]
      else
        let attribs = try List.assoc lbl (nodes_of_graph env.types |> List.map (fun (DBN (l, a)) -> (l, a)))
                      with Not_found -> [] in
        let expected_type = try List.assoc fn attribs with Not_found -> BoolT (* Valeur par défaut temporaire *) in
        begin match check_expr e expected_type env with
        | Result.Ok _ -> Result.Ok env
        | Result.Error errs -> Result.Error errs
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
  