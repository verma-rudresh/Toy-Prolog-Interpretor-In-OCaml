(* File calc.ml *)
open Tree
open Types
open Printf

let table = 
    let filename = Sys.argv.(1) in 
    let file = open_in filename in
    let lexbuf = Lexing.from_channel file in
    let rec createTable acc = 
      let result = Parser.main Lexer.token lexbuf in
        match result with (Node(S("file_end",0),[]),[]) -> acc
        | _ -> (createTable (result::acc)) 
      in 
    (createTable [])
;;

(* printTable table;; *)
let _ = 
  Printf.printf "?-"; flush stdout;
  let lexbuf = Lexing.from_channel stdin in
    while true do
      let result = Parser.main Lexer.token lexbuf in
        match result with 
        (Node(S("exit",0), []), [Node(S("true",0),[])]) -> Printf.printf "EXITING\n";flush stdout; exit 0
        |(goal, [Node(S("true",0),[])]) ->(
          let targets = (vars goal) in
          match (eval_query [goal] table (false,[]) targets) with 
          (true,sl) ->   Printf.printf "TRUE.\n\n?-"; flush stdout;
          |(false,sl) -> Printf.printf "FALSE.\n";Printf.printf "\n?-"; flush stdout;
        ) 
        | _-> Printf.printf "INVALID INPUT GOAL\n";Printf.printf "\n?-"; flush stdout;
    done
;;