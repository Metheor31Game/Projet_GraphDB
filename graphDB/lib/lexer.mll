{
  open Lexing
  open Parser
  open Lang
  exception Lexerror

  (* for cutting off the trailing quotes of strings *)
  let clean_string s = String.sub s 1 (String.length s - 2) ;;

  let pos lexbuf = (lexeme_start lexbuf, lexeme_end lexbuf)

  let advance_line_pos pos =
    { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum; }

  let advance_line lexbuf =
    lexbuf.lex_curr_p <- advance_line_pos lexbuf.lex_curr_p

}

let alph =           ['a'-'z''A'-'Z']
let num  =           ['0'-'9'] 
let decimal	=	'0'|(['1'-'9']['0'-'9']*)
let comment = '(' '*' [^'*']* ('*' (('*'*)|([^'*'')'][^'*']*)))* '*' ')'
(* To keep things simple, strings here only contain chars, nums and blanks 
  Could be refined *)
let stringchar = alph|num|' '
let string = '"' stringchar* '"'     

rule token = parse
 [' ' '\t']
    { token lexbuf }    (* white space: recursive call of lexer *)
|'\n'
    {advance_line lexbuf; token lexbuf }    (* white space: recursive call of lexer *)
| comment
    { token lexbuf }    (* comment --> ignore *)
| decimal  as i	  { INTCONSTANT (int_of_string i)}
| '{'  { LBRACE }
| '}'  { RBRACE }
| '['  { LBRACKET }
| ']'  { RBRACKET }
| '('  { LPAREN }
| ')'  { RPAREN }
| '.'  { DOT }
| ','  { COMMA }
| ':'  { COLON }

| "true"       {BCONSTANT true}
| "false"      {BCONSTANT false}

| "create"     {CREATE}
| "delete"     {DELETE}
| "match"      {MATCH}
| "return"     {RETURN}
| "set"        {SET}
| "where"      {WHERE}

| "->"         {ARROW}

| '+'          { ADD }
| '-'          { SUB }
| '*'          { MUL }
| '/'          { DIV }
| "mod"        { MOD }

| '='          {EQ}
| ">="         {GE}
| '>'          {GT}
| "<="         {LE}
| '<'          {LT}
| "<>"         {NE}

| "and"        {BLAND}
| "or"         {BLOR}

| eof          {EOF}

| "bool"       {TP(BoolT)}
| "int"        {TP(IntT)}
| "string"     {TP(StringT)}

| alph(alph|num)* as i  {IDENTIFIER i}
| string as s {STRINGCONSTANT (clean_string s)}

| _  {Printf.printf "ERROR: unrecogized symbol '%s'\n" (Lexing.lexeme lexbuf);
      raise Lexerror }

and
    ruleTail acc = parse
| eof { acc }
| _* as str { ruleTail (acc ^ str) lexbuf }
