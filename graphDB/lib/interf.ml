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
  (* Définir un graphe de types valide *)
  let gt = DBG (
    [DBN ("P", [("nom", StringT); ("age", IntT)]);
     DBN ("E", [("pme", BoolT)])],
    [DBR ("P", "ami", "P"); DBR ("P", "emp", "E")]
  ) in
  let env = initial_environment gt in
  
  (* Liste d'instructions à tester *)
  let tests = [
    (* Cas valide : création d'un nœud *)
    IActOnNode (CreateAct, "marie", "P");
    (* Cas valide : création d'un nœud *)
    IActOnNode (CreateAct, "ab", "E");
    (* Cas valide : relation entre deux variables existantes *)
    IActOnRel (CreateAct, "marie", "emp", "ab");
    (* Cas invalide : variable déjà liée *)
    IActOnNode (CreateAct, "marie", "P");
    (* Cas invalide : type de nœud non déclaré *)
    IActOnNode (CreateAct, "pierre", "X");
    (* Cas invalide : relation non déclarée *)
    IActOnRel (CreateAct, "marie", "f", "ab")
  ] in
  
  (* Exécuter les tests et afficher les résultats *)
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
            run_tests env rest  (* On continue avec l'environnement actuel *)
  in
  run_tests env tests

(* Modifier run_interactive pour inclure le test *)
let run_interactive () =
  (* test_check_graph_types (); *)
  test_tc_instr ();
  while true do
    Printf.printf ">> %!";
    let e = run_parser_error_reporting None in
    Printf.printf "%s\n" (Lang.show_prog e)
  done


(* Run the file with name fn (a string),
   including parsing, type checking, displaying the output
 *)
let run_file fn = 
  let p = run_parser_error_reporting (Some fn) in
  let np = Typing.typecheck true (Instr.normalize_prog p) in 
  let State(g, tab, _mn) = Sem.exec np in 
  Printf.printf "%s\n" (Sem.show_db_graph_struct g);
  Printf.printf "%s\n" (Sem.show_vname_nodeid_table tab);
  Display.output_table tab;
  Display.output_graph_struct g

(* Print the help message *)
let print_help () = print_string "Run as:\n Code_Graph [h | i | f <filename> ] \n "

