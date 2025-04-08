(* open Proj_GraphDB.Interf *)

(* dune exec messes up the options if they are written -i, -f etc. *)
(* let main () = 
  if Array.length Sys.argv <= 1
  then print_help ()
  else match Sys.argv.(1) with
    | "i" -> run_interactive ()
    | "f" -> 
      if Array.length Sys.argv <= 2
      then print_help ()
      else run_file (Sys.argv.(2))
    | _ -> print_help () *)

    
(* let () = main () *)

(* ----------------------------------------------------------------- *)

(* Importation des modules nécessaires pour l'exécutable *)
open Proj_GraphDB.Lang      (* Types de base comme prog, query, clause *)
open Proj_GraphDB.Instr     (* Normalisation des programmes *)
open Proj_GraphDB.Typing    (* Vérification des types *)
open Proj_GraphDB.Sem       (* Sémantique et évaluation *)
open Proj_GraphDB.Display   (* Affichage du graphe et de la table *)

(* Module local pour l'analyse lexicale et syntaxique *)
module MyParser = struct
  (* Fonction pour parser une chaîne MiniGQL en un programme Lang.prog *)
  let parse_string (s : string) : prog =
    let lexbuf = Lexing.from_string s in  (* Crée un buffer lexical à partir de la chaîne *)
    try
      (* Appelle le parser généré par Menhir avec les tokens du lexer *)
      Proj_GraphDB.Parser.main Proj_GraphDB.Lexer.token lexbuf
    with
    | Proj_GraphDB.Lexer.Lexerror -> 
        failwith "Lexical error"  (* Erreur si le lexer rencontre un symbole invalide *)
    | Proj_GraphDB.Parser.Error -> 
        failwith ("Syntax error at position " ^ string_of_int (Lexing.lexeme_start lexbuf))
        (* Erreur si la syntaxe est incorrecte, avec la position *)
end

(* Fonction principale qui traite un programme MiniGQL *)
let process_program (prog : prog) =
  (* Transforme le programme en une forme normalisée avec des instructions simples *)
  let norm_prog = normalize_prog prog in
  
  (* Vérifie que le programme normalisé est bien typé *)
  match typecheck false norm_prog with
  | Result.Error errs ->
      (* Si des erreurs de typage sont détectées, les affiche et arrête *)
      Printf.printf "Type errors:\n%s\n" (String.concat "\n" errs);
      exit 1
  | Result.Ok _ ->
      (* Exécute le programme normalisé à partir de l'état initial *)
      let final_state = exec norm_prog in
      
      (* Extrait le graphe et la table de l'état final pour les afficher *)
      match final_state with
      | State (g, t, _) ->
          output_graph_struct g;  (* Génère graph.pdf avec le graphe *)
          output_table t          (* Génère table.pdf avec la table *)

(* Fonction principale qui gère les modes d'exécution *)
let main () =
  let args = Sys.argv in  (* Récupère les arguments de la ligne de commande *)
  match Array.length args with
  | 2 when args.(1) = "1" ->
      (* Mode interactif : dune exec Proj_GraphDB 1 *)
      print_endline "Enter MiniGQL program (Ctrl-D to finish):";
      let input = ref "" in  (* Accumule l'entrée ligne par ligne *)
      (try
        while true do
          input := !input ^ (read_line ()) ^ "\n"  (* Lit jusqu'à Ctrl-D *)
        done
      with End_of_file -> ());
      let prog = MyParser.parse_string !input in  (* Parse l'entrée *)
      process_program prog  (* Traite le programme *)

  | 3 when args.(1) = "f" ->
      (* Mode batch : dune exec Proj_GraphDB f <fichier> *)
      let filename = args.(2) in  (* Récupère le nom du fichier *)
      let ic = open_in filename in  (* Ouvre le fichier *)
      let content = really_input_string ic (in_channel_length ic) in  (* Lit tout *)
      close_in ic;  (* Ferme le fichier *)
      let prog = MyParser.parse_string content in  (* Parse le contenu *)
      process_program prog  (* Traite le programme *)

  | _ ->
      (* Cas d'usage invalide : affiche les instructions *)
      Printf.printf "Usage:\n";
      Printf.printf "  dune exec Proj_GraphDB 1          # Interactive mode\n";
      Printf.printf "  dune exec Proj_GraphDB f <file>   # Batch mode\n";
      exit 1

(* appel de la fonction main | Lancement de l'exécutable *)
let () = main ()