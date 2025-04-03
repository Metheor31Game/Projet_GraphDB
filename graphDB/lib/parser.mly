
%token <string> IDENTIFIER
%token <Lang.attrib_tp> TP
%token <bool> BCONSTANT
%token <int> INTCONSTANT
%token <string> STRINGCONSTANT
%token BLAND BLOR
%token EQ GE GT LE LT NE
%token ADD SUB MUL DIV MOD
%token LBRACE RBRACE LBRACKET RBRACKET LPAREN RPAREN 
%token DOT COMMA COLON
%token CREATE DELETE MATCH RETURN SET WHERE
%token ARROW
%token EOF

%start<Lang.prog> main

%left BLOR
%left BLAND
%left EQ GE GT LE LT NE
%left ADD SUB
%left MUL DIV MOD

%{ open Lang %}

%%

main: prog EOF { $1 }

prog: td = list(tpDecl);  q = query 
     { let (nts, rts) = List.partition_map Fun.id td in Prog (DBG(nts, rts), q) }

tpDecl:
| n = nodeTpDecl { Either.Left n }
| r = relTpDecl { Either.Right r }


query: cls = list(clause) { Query cls }

/* TODO: to be completed */
clause: 
| CREATE; pts = separated_list(COMMA, pattern) { Create pts }
| MATCH; pts = separated_list(COMMA, pattern) { Match pts }
| DELETE; dp = delete_pattern { Delete dp }
| RETURN; vns = separated_list(COMMA, IDENTIFIER) { Return vns }
| WHERE; e = expr { Where e }
| SET; assignment = separated_list(COMMA, assignment_pattern) { Set assignment }

/* TODO: to be completed */
pattern: 
| np = node_pattern { SimpPattern np }
| np = node_pattern; SUB; LBRACKET; COLON; lbl = IDENTIFIER; RBRACKET; ARROW; p = pattern {CompPattern(np, lbl, p)}

node_pattern: 
| LPAREN; v = IDENTIFIER; COLON; t = IDENTIFIER; RPAREN { DeclPattern(v, t) }
| LPAREN; v = IDENTIFIER; RPAREN { VarRefPattern(v) }

delete_pattern:
| vns = separated_nonempty_list(COMMA, IDENTIFIER ) { DeleteNodes vns }
| rls = separated_nonempty_list(COMMA, relation_pattern) { DeleteRels rls }

relation_pattern:
| v1 = IDENTIFIER; SUB; LBRACKET; COLON; lbl = IDENTIFIER; RBRACKET; ARROW; v2 = IDENTIFIER { (v1, lbl, v2) }

assignment_pattern:
| vn = IDENTIFIER; DOT; fn = IDENTIFIER; EQ; e = expr { (vn, fn, e) }

/* Expressions */

primary_expr: //constante et accès à un champs
| vn = IDENTIFIER; DOT; fn = IDENTIFIER 
     { AttribAcc(vn, fn) }
| c = BCONSTANT
     { Const(BoolV(c)) }
| c = INTCONSTANT
     { Const(IntV(c)) }
| c = STRINGCONSTANT
     { Const(StringV(c)) }
| LPAREN e = expr RPAREN
     { e }

binop:
| op = barith; { BArith op }
| op = bcompar; { BCompar op }
| op = blogic; { BLogic op }

barith:
| ADD  { BAadd }
| SUB  { BAsub }
| MUL  { BAmul }
| DIV  { BAdiv }
| MOD  { BAmod }

bcompar:
| EQ  { BCeq }
| GE  { BCge }
| GT  { BCgt }
| LE  { BCle }
| LT  { BClt }
| NE  { BCne }

blogic:
| BLAND { BLand }
| BLOR  { BLor }

/* TODO: to be completed */
expr:
| a = primary_expr { a }
| e1 = expr; op = binop; e2 = expr { BinOp (op, e1, e2) }


/* Types */
nodeTpDecl: LPAREN; COLON; i = IDENTIFIER; a = attrib_declList; RPAREN  { DBN (i, a) }

attrib_decl: i = IDENTIFIER; t = TP { (i, t) }
attrib_declList: 
| LBRACE; ads = separated_list(COMMA, attrib_decl); RBRACE { ads }


/* Relational type declarations of the form (:nt1) -[:rt]-> (:nt2)
 */
nodeTpRef: LPAREN; COLON; si = IDENTIFIER; RPAREN { si }
relTpDecl: si = nodeTpRef;
           SUB; LBRACKET; COLON; rlab = IDENTIFIER; RBRACKET; ARROW; 
           ti = nodeTpRef
           { Graphstruct.DBR (si, rlab, ti) }

%%
