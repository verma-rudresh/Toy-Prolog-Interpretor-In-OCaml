(* File lexer.mll *)
{
open Parser        (* The type token is defined in parser.mli *)
exception Eof
}
rule token = parse
    [' ' '\t' '\n']     { token lexbuf }     (* skip blanks *)
  | ['.' ]        { EOL }
  | [',' ]        { COMMA }
  | '('                                                              { LP                             }
  | ')'                                                              { RP                             }
  | ":-"                                                             { IFF                            }
  | ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_' ''']*    as ided          { VAR (ided)                      }
  | ['a'-'z' '0'-'9']['-' '>' '+' '/' '-' '*' 'a'-'z' 'A'-'Z' '0'-'9' '_' ''']*    as ided          { ID (ided)                      }
  | eof {EOF}