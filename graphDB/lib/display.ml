(* Display graphs with Graphviz / Dot *)
(* Documentation: see 
https://ocaml.org/p/ocamlgraph/2.0.0/doc/index.html
https://github.com/backtracking/ocamlgraph/
https://stackoverflow.com/questions/8999557/how-to-visualize-draw-automata-in-ocaml
*)

module DBNode = struct
  type t = Graphstruct.nodeid * Sem.attrib_struct
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

(* representation of an edge -- must be comparable *)
module DBEdge = struct
  type t = Lang.label
  let compare = compare
  let equal = (=)
  let default = ""
end

(* Display graph *)
module DisplayGraph = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(DBNode)(DBEdge)

let quote_string s = "\\\"" ^ s ^ "\\\""
let pretty_value = function
| Lang.BoolV b -> string_of_bool b
| Lang.IntV i -> string_of_int i
| Lang.StringV s -> quote_string s

let dot_display_attrib (fn, vl) = fn ^ " " ^ (pretty_value vl)

let dot_display_attribs attribs = 
  "{" ^ (String.concat ", " (List.map dot_display_attrib attribs)) ^ "}"

let dot_display_vertex_label (n: Graphstruct.nodeid) (i: Sem.attrib_struct) = 
  let (lb, attribs) = i in
  (string_of_int n) ^ ":" ^ lb ^ (dot_display_attribs attribs)

let dot_display_edge_label _s e _t = e

(* module for creating dot-files *)
module Dot = Graph.Graphviz.Dot(struct
  include DisplayGraph (* use the graph module from above *)
  let edge_attributes (s, e, t) = [`Label (dot_display_edge_label s e t); `Color 0xFF]
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let vertex_attributes (n, i) = 
    [`Fontcolor 0xFF0000; `Shape `Box; `Label (dot_display_vertex_label n i)]
  let vertex_name (n, _i) =  (string_of_int n)
  let default_vertex_attributes _ = []
 let graph_attributes _ = []
end)

let add_vertices = List.fold_left DisplayGraph.add_vertex
let add_edges = List.fold_left DisplayGraph.add_edge_e


let convert_to_vertex (Graphstruct.DBN (n, i)) = (n, i)

let convert_to_info_edge vsi (Graphstruct.DBR (n1, r, n2)) = 
  ((n1, List.assoc n1 vsi), r, (n2, List.assoc n2 vsi))


let convert_to_display_graph (g: Sem.db_graph_struct) = 
  match g with
  DBG(ns, rs) -> 
    let vs = List.map convert_to_vertex ns in
    let es = List.map (convert_to_info_edge vs) rs in
    add_edges (add_vertices DisplayGraph.empty vs) es

let output_graph_to_stdout vs es = 
  Dot.output_graph stdout (add_edges (add_vertices DisplayGraph.empty vs) es)
    
let output_graph_to_file outfile_name dispg = 
  let outfile = open_out outfile_name in 
  Dot.output_graph outfile dispg; close_out outfile

let output_graph_struct g = 
  let fn = "graph" in
  let dotfile = fn ^ ".dot" in
  let pdffile  = fn ^ ".pdf" in
  output_graph_to_file dotfile (convert_to_display_graph g);
  let _ = Sys.command ("dot -Tpdf " ^ dotfile ^ " -o " ^ pdffile) in 
  ()


let column_format n = if n = 0 then "l" else String.make n 'l'

let table_header vs = (String.concat "&" vs) ^ "\\\\\n\\hline\n"
let table_lines lss = String.concat "\\\\\n" 
    (List.map (fun ls -> (String.concat "&"  (List.map string_of_int ls))) lss)

let table_body vs lss = 
  match vs with 
  | [] -> "- \\\\ \\hline  -"
  | _ -> table_header vs ^ table_lines lss ^ "\n"

(* Output table in Latex. 
Special treatment for empty table because Latex does not like 0-column tables *)
let display_table (Sem.Table(vs, lss)) =
  let pre = "\\documentclass{article}[12pt]\n\\begin{document}\n\\centering\n\\begin{tabular}{"
    ^ (column_format (List.length vs))  ^ "}\n" in
  let body = table_body vs lss in
  let post = "\\end{tabular}\n
  \\end{document}\n" in
 pre ^ body ^ post

let output_table_to_file outfile_name tabstr = 
  let outfile = open_out outfile_name in 
  Printf.fprintf outfile "%s\n" tabstr; close_out outfile

  (* Output table to a *tex file and launch pdflatex silently (output to /dev/null) *)
let output_table tab = 
  let fn = "table" in
  let texfile = fn ^ ".tex" in
  output_table_to_file texfile (display_table tab);
  let _ = Sys.command ("pdflatex " ^ texfile ^ "  > /dev/null") in 
  ()