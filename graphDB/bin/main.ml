open Proj_GraphDB.Interf

(* dune exec messes up the options if they are written -i, -f etc. *)
let main () = 
  if Array.length Sys.argv <= 1
  then print_help ()
  else match Sys.argv.(1) with
    | "i" -> run_interactive ()
    | "f" -> 
      if Array.length Sys.argv <= 2
      then print_help ()
      else run_file (Sys.argv.(2))
    | _ -> print_help ()

 
 (* ---------------------------------------------------------------- *)

let () = main ()

