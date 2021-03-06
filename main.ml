open River
open Lexer
open Parser
open Arg
open Printf


let parseProgram c = 
    try let lexbuf = Lexing.from_channel c in  
            parser_main lexer_main lexbuf 
    with Parsing.Parse_error -> failwith "Parse failure!" ;;


let rec readIntoBufferRec s =
  try let line = (input_line stdin) in
   (readIntoBufferRec ( line :: s)) with End_of_file ->  s
;;

let readIntoBuffer () = readIntoBufferRec([]);;

(* Parsing.set_trace true;; *)
let arg = ref stdin in
let setProg p = arg := open_in p in
let usage = "./main PROGRAM_FILE" in
parse [] setProg usage ; 
let parsedProg = parseProgram !arg in
(* print_string "Program Parsed" ; print_newline(); *)
(* Run Type Checker *)
let _ = typeProg parsedProg in
let () = 
(* print_string "Program Type Checked";  *)
print_newline() in
(* Run Evaluator *)
let readBuffer = readIntoBuffer() in 
let result1 = evalProg readBuffer parsedProg in 
(* print_string "Program Evaluated using Machine semantics to ==> " ;  *)print_res result1 ; print_newline();
flush stdout
