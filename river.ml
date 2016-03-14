exception LookupError ;;
exception TypeError ;;
exception UnboundVariableError;;
exception Terminated ;;
exception StuckTerm ;;
exception NonBaseTypeResult;;

open Printf;;

(* Types of the language *)
type rivType = RivInt | RivStream | RivFun of rivType * rivType

(* Grammar of the languge *)
type rivTerm = 
	  TmNum of int
	| TmStream of stream
	| TmLessThan of rivTerm * rivTerm
	