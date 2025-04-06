(* Interface functionality with the parser, contains the essential 
   functions for bin/main.ml
*)

open Graphstruct
open Lang
open Typing
open Instr

exception ParseLexError of exn * (int * int * string * string)

(* Run parser by reading from lex buffer, 
   raise ParseLexError in case of error
 *)
let run_parser lexbuf = 
  try
    Parser.main Lexer.token lexbuf
  with exn ->
    begin
      let curr = lexbuf.Lexing.lex_curr_p in
      let line = curr.Lexing.pos_lnum in
      let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      let tok = Lexing.lexeme lexbuf in
      let tail =  Lexer.ruleTail "" lexbuf in 
      raise (ParseLexError (exn,(line,cnum,tok,tail)))
    end

let print_parse_error fn_option (line,cnum,tok,tail) =
  print_string ((match fn_option with None -> "" | Some fn -> "Parsing error in file: " ^ fn) ^ 
                      " on line: " ^ (string_of_int line) ^ 
                      " column: " ^ (string_of_int cnum) ^
                      " token: "  ^ tok ^
                      "\nrest: "  ^ tail ^ "\n")
;;

(* Run parser either reading from standard in (for fn_option = None)
   or reading from a file name (for fn_option = Some fn)
   and report errors in a readable format
 *)
let run_parser_error_reporting fn_option = 
  let chan = (match fn_option with 
               None -> (Stdlib.stdin)
              | Some fn -> open_in fn) in
  let lexbuf = Lexing.from_channel chan in 
  try run_parser lexbuf
  with ParseLexError (_e, errinfo) -> 
    print_parse_error fn_option errinfo;
    failwith "Stopped execution."
;;

(* Fonction de test pour la fonction check_graph_types*)
let test_check_graph_types () =
  let gt = DBG (
    [DBN ("P", [("nom", StringT)]); DBN ("P", [("age", IntT)]); DBN ("E", [])],  (* Doublon sur "P" *)
    [DBR ("P", "ami", "P"); DBR ("P", "emp", "X")]  (* "X" non déclaré *)
  ) in
  match Typing.check_graph_types gt with
  | Result.Ok () -> Printf.printf "Graph types are valid!\n"
  | Result.Error errs -> Printf.printf "Errors:\n%s\n" errs

(* Fonction de test pour tc_instr *)
let test_tc_instr () =
  let gt = DBG (
    [DBN ("P", [("nom", StringT); ("age", IntT)]);
     DBN ("E", [("pme", BoolT)])],
    [DBR ("P", "ami", "P"); DBR ("P", "emp", "E")]
  ) in
  let env = initial_environment gt in
  let tests = [
    IActOnNode (CreateAct, "marie", "P");
    IActOnNode (CreateAct, "ab", "E");
    IActOnRel (CreateAct, "marie", "emp", "ab");
    IActOnNode (CreateAct, "marie", "P");
    IActOnNode (CreateAct, "pierre", "X");
    IActOnRel (CreateAct, "marie", "f", "ab")
  ] in
  let rec run_tests env = function
    | [] -> Printf.printf "All tests completed!\n"
    | instr :: rest ->
        Printf.printf "Testing: %s\n" (show_instruction instr);
        match tc_instr instr env with
        | Result.Ok new_env ->
            Printf.printf "Success: Environment updated\n%s\n" (show_environment new_env);
            run_tests new_env rest
        | Result.Error errs ->
            Printf.printf "Error:\n%s\n" (String.concat "\n" errs);
            run_tests env rest
  in
  run_tests env tests

(* Fonction de test pour tc_instrs_stop *)
let test_tc_instrs_stop () =
  let gt = DBG (
    [DBN ("P", [("nom", StringT); ("age", IntT)]);
     DBN ("E", [("pme", BoolT)])],
    [DBR ("P", "ami", "P"); DBR ("P", "emp", "E")]
  ) in
  let env = Typing.initial_environment gt in
  let instrs = [
    IActOnNode (CreateAct, "marie", "P");
    IActOnNode (CreateAct, "ab", "E");
    IActOnRel (CreateAct, "marie", "emp", "ab");
    IActOnNode (CreateAct, "marie", "P");
    IActOnRel (CreateAct, "marie", "f", "ab");
    IDeleteNode "pierre"
  ] in
  Printf.printf "Testing tc_instrs_stop with %d instructions:\n" (List.length instrs);
  List.iter (fun i -> Printf.printf "- %s\n" (show_instruction i)) instrs;
  match Typing.tc_instrs_stop instrs env with
  | Result.Ok final_env ->
      Printf.printf "Success: All instructions valid\nFinal environment:\n%s\n" (Typing.show_environment final_env)
  | Result.Error errs ->
      Printf.printf "Errors detected:\n%s\n" (String.concat "\n" errs)

(* Fonction de test pour tc_instrs_stop_immediate *)
let test_tc_instrs_stop_immediate () =
  let gt = DBG (
    [DBN ("P", [("nom", StringT); ("age", IntT)]);
     DBN ("E", [("pme", BoolT)])],
    [DBR ("P", "ami", "P"); DBR ("P", "emp", "E")]
  ) in
  let env = Typing.initial_environment gt in
  let instrs = [
    IActOnNode (CreateAct, "marie", "P");
    IActOnNode (CreateAct, "ab", "E");
    IActOnRel (CreateAct, "marie", "emp", "ab");
    IActOnNode (CreateAct, "marie", "P");
    IActOnRel (CreateAct, "marie", "f", "ab");
    IDeleteNode "pierre"
  ] in
  Printf.printf "Testing tc_instrs_stop_immediate with %d instructions:\n" (List.length instrs);
  List.iter (fun i -> Printf.printf "- %s\n" (show_instruction i)) instrs;
  match Typing.tc_instrs_stop_immediate instrs env with
  | Result.Ok final_env ->
      Printf.printf "Success: All instructions valid\nFinal environment:\n%s\n" (Typing.show_environment final_env)
  | Result.Error errs ->
      Printf.printf "Errors detected (stopped at first):\n%s\n" (String.concat "\n" errs)

(* Fonction de test pour typecheck *)
let test_typecheck () =
  let gt = DBG (
    [DBN ("P", [("nom", StringT)]); DBN ("E", [])],
    [DBR ("P", "emp", "E")]
  ) in
  let prog = NormProg (gt, NormQuery [
    IActOnNode (CreateAct, "marie", "P");
    IActOnNode (CreateAct, "ab", "E");
    IActOnRel (CreateAct, "marie", "emp", "ab");
    IActOnNode (CreateAct, "marie", "P");
    IActOnRel (CreateAct, "marie", "f", "ab")
  ]) in
  Printf.printf "Testing typecheck with continue = true:\n";
  begin match Typing.typecheck true prog with
  | Result.Ok env -> Printf.printf "Success: Program valid\nFinal environment:\n%s\n" (Typing.show_environment env)
  | Result.Error errs -> Printf.printf "Errors (all accumulated):\n%s\n" (String.concat "\n" errs)
  end;
  Printf.printf "\nTesting typecheck with continue = false:\n";
  begin match Typing.typecheck false prog with
  | Result.Ok env -> Printf.printf "Success: Program valid\nFinal environment:\n%s\n" (Typing.show_environment env)
  | Result.Error errs -> Printf.printf "Errors (stopped at first):\n%s\n" (String.concat "\n" errs)
  end

(* Extrait un norm_prog depuis un tc_result, échoue avec un message en cas d'erreur
   Necessaire pour le test de typecheck sinon run_file ne fonctionne pas *)
let unwrap_typecheck (tc_res : Typing.tc_result) (np : norm_prog) : norm_prog =
  match tc_res with
  | Result.Ok _env -> np
  | Result.Error errs ->
      Printf.printf "Typecheck errors:\n%s\n" (String.concat "\n" errs);
      failwith "Stopped execution due to type errors"

(* Run the file with name fn (a string),
   including parsing, type checking, displaying the output
 *)
let run_file fn = 
  let p = run_parser_error_reporting (Some fn) in
  let np = Instr.normalize_prog p in
  let tc_res = Typing.typecheck true np in
  let checked_np = unwrap_typecheck tc_res np in
  let State(g, tab, _mn) = Sem.exec checked_np in 
  Printf.printf "%s\n" (Sem.show_db_graph_struct g);
  Printf.printf "%s\n" (Sem.show_vname_nodeid_table tab);
  Display.output_table tab;
  Display.output_graph_struct g

let run_interactive () =
  (* test_check_graph_types (); *)
  (* test_tc_instr (); *)
  (* test_tc_instrs_stop(); *)
  (* test_tc_instrs_stop_immediate (); *)
  test_typecheck ();
  while true do
    Printf.printf ">> %!";
    let e = run_parser_error_reporting None in
    Printf.printf "%s\n" (Lang.show_prog e)
  done

(* Print the help message *)
let print_help () = print_string "Run as:\n Code_Graph [h | i | f <filename> ] \n "