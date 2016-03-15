exception LookupError ;;
exception TypeError ;;
exception UnboundVariableError;;
exception Terminated ;;
exception StuckTerm ;;
exception NonBaseTypeResult;;

open Printf;;

(* Stream implementation *)
type 'a stream = Stream of 'a * (unit -> 'a stream) | StreamEnd of 'a;;
let hd : 'a stream -> 'a = function Stream (a, _) -> a;;
let tl : 'a stream -> 'a stream = function Stream (_, s) -> s ();;


(* Types of the language *)
type rivType =  RivInt | RivBool | RivFun of rivType * rivType | RivStream of rivType 

(* Grammar of the language *)
type rivTerm =
    RmNum of int stream
  | RmVar of string
  | RmUMinus of rivTerm
  | RmMinus of rivTerm * rivTerm
  | RmApp of rivTerm * rivTerm
  | RmPlus of rivTerm * rivTerm
  | RmMultiply of rivTerm * rivTerm
  | RmDivide of rivTerm * rivTerm 
  | RmLessThan of rivTerm * rivTerm
  | RmGreaterThan of rivTerm * rivTerm
  | RmGreaterEqualTo of rivTerm * rivTerm
  | RmLessEqualTo of rivTerm * rivTerm
  | RmNotEqualTo of rivTerm * rivTerm
  | RmEqualTo of rivTerm * rivTerm
  | RmCons of rivTerm  * rivTerm
  | RmAppend of rivTerm * rivTerm
  | RmIndex of string * rivTerm
  | RmSection of string * rivTerm * rivTerm
  | RmSectionStart of string * rivTerm
  | RmSectionEnd of string * rivTerm
  | RmIf of rivTerm * rivTerm * rivTerm
  (* Let: item Type * item Name * Expression for the item * Expression *)
  | RmLet of rivType * string * rivTerm * rivTerm
  (* Lambda: Return Type * Parameter Type * Parameter Name * Expression *)
  | RmLbd of rivType * rivType * string * rivTerm

let rec isValue e = print_string "isValue called\n"; match e with
  | RmNum(s) -> true
  | RmLbd(rT,tT,x,e') -> true
  | _ -> false
;;

(* Type of Environments *)
type 'a context = Env of (string * 'a) list
type typeContext = rivType context
type valContext = rivTerm context

(* Function to look up the type of a string name variable in a type environment *)
let rec lookup env str = match env with
   Env [] -> raise LookupError
  |Env ((name,thing) :: gs) ->
  (
    match (name = str) with
    true -> thing
    |false -> lookup (Env (gs)) str
  )
;;

(* Function to add an extra entry in to an environment *)
let addBinding env str thing = match env with
Env(gs) -> Env ( (str, thing) :: gs ) ;;

(* Return True if the variable x is used in e *)
let rec free e x = match e with
  RmVar(y) -> (x=y)
  |RmNum(s) -> false
  |RmIf(t1,t2,t3) -> (free t1 x) || (free t2 x) || (free t3 x)
  |RmLessThan(e1,e2) -> (free e1 x) || (free e2 x)
  |RmLessEqualTo(e1,e2) -> (free e1 x) || (free e2 x)
  |RmGreaterThan(e1,e2) -> (free e1 x) || (free e2 x)
  |RmGreaterEqualTo(e1,e2) -> (free e1 x) || (free e2 x)
  |RmEqualTo(e1,e2) -> (free e1 x) || (free e2 x)
  |RmPlus(e1,e2) -> (free e1 x) || (free e2 x)
  |RmMinus(e1,e2) -> (free e1 x) || (free e2 x)
  |RmMultiply(e1,e2) -> (free e1 x) || (free e2 x)
  |RmDivide(e1,e2) -> (free e1 x) || (free e2 x)
  |RmUMinus(e1) -> (free e1 x)
  |RmApp(e1,e2) -> (free e1 x) || (free e2 x)
  |RmLbd(rT,tT,y,e1) when (x=y) -> false
  |RmLbd(rT,tT,y,e1)            -> (free e1 x)
  |RmLet(tT,y,e1,e2) when (x=y) -> (free e1 x) 
  |RmLet(tT,y,e1,e2)            -> (free e1 x) || (free e2 x)
;;

let rename (s:string) = s^"'";;

(* Substitute e1 as 'x' in e2 *)
let rec subst e1 x e2 = match e2 with
  | RmVar(y) when (x=y) -> e1
  | RmVar(y) -> RmVar(y)
  | RmNum(s) -> RmNum(s)
  (* Substitute all the parameters *)
  | RmIf(b,e21,e22) -> RmIf( (subst e1 x b) , (subst e1 x e21) , (subst e1 x e22) )
  | RmLessThan(e21, e22) -> RmLessThan( (subst e1 x e21) , (subst e1 x e22) )
  | RmLessEqualTo(e21, e22) -> RmLessEqualTo( (subst e1 x e21) , (subst e1 x e22) )
  | RmGreaterThan(e21, e22) -> RmGreaterThan( (subst e1 x e21) , (subst e1 x e22) )
  | RmGreaterEqualTo(e21, e22) -> RmLessEqualTo( (subst e1 x e21) , (subst e1 x e22) )
  | RmEqualTo(e21, e22) -> RmEqualTo( (subst e1 x e21) , (subst e1 x e22) )
  | RmNotEqualTo(e21, e22) -> RmNotEqualTo( (subst e1 x e21) , (subst e1 x e22) )
  | RmPlus(e21, e22) -> RmPlus( (subst e1 x e21) , (subst e1 x e22) )
  | RmMinus(e21, e22) -> RmMinus( (subst e1 x e21) , (subst e1 x e22) )
  | RmMultiply(e21, e22) -> RmMultiply( (subst e1 x e21) , (subst e1 x e22) )
  | RmDivide(e21, e22) -> RmDivide( (subst e1 x e21) , (subst e1 x e22) )
  | RmUMinus(e21) -> RmUMinus( (subst e1 x e21) )
  | RmApp(e21, e22) -> RmApp( (subst e1 x e21) , (subst e1 x e22) )

  | RmLbd(rT,tT,y,e21) when (x=y) -> RmLbd(rT,tT,y,e21)

  (*if the variable passed into the lambda is the value, substitute it*)
  | RmLbd(rT,tT,y,e21) when (not (free e1 y)) -> RmLbd(rT,tT,y,subst e1 x e21)

  (* Rename if it isn't free *)
  | RmLbd(rT,tT,y,e21) when (free e1 y) -> let yy = rename y in subst e1 x (RmLbd(rT, tT, yy, (subst (RmVar(yy)) y e21)))

  | RmLet(tT,y,e21,e22) when (x=y) -> RmLet(tT,y,e21,e22)
  | RmLet(tT,y,e21,e22) when (not(free e1 y)) -> RmLet(tT, y, subst e1 x e21 , subst e1 x e22)
  (* Rename a variable if it isn't free *)
  | RmLet(tT,y,e21,e22) when ((free e1 y)) -> let yy = rename y in subst e1 x ( RmLet(tT, yy, subst (RmVar(yy)) y e21 , subst (RmVar(yy)) y e22) )
;;

let rec eval1S e = match e with
  | (RmVar x) -> print_string "VARIABLE: "; print_string x; print_string "\n"; raise Terminated
  | RmNum(Stream(n,_)) -> print_string "NUMBER: "; print_int n; print_string "\n"; raise Terminated
  | RmNum(StreamEnd(n)) -> print_string "END: "; print_int n; print_string "\n"; raise Terminated
  | (RmLbd(rT,tT,y,e')) -> raise Terminated

  (* Conditionals *)
  (* TODO Implement streams properly!*)
  | (RmLessThan(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> if n<m then RmNum(StreamEnd(1)) else RmNum(StreamEnd(0))
  | (RmLessThan(RmNum(Stream(n,m)), e2))      -> let e2' = (eval1S e2) in RmLessThan(RmNum(Stream(n,m)),e2')
  | (RmLessThan(e1, e2))            -> let e1' = (eval1S e1) in RmLessThan(e1',e2)

  (* TODO Implement streams properly!*)
  | (RmLessEqualTo(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> if n<=m then RmNum(StreamEnd(1)) else RmNum(StreamEnd(0));
  | (RmLessEqualTo(RmNum(s), e2))      -> let e2' = (eval1S e2) in RmLessEqualTo(RmNum(s),e2')
  | (RmLessEqualTo(e1, e2))            -> let e1' = (eval1S e1) in RmLessEqualTo(e1',e2)

  (* TODO Implement streams properly!*)
  | (RmGreaterThan(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> if n>m then RmNum(StreamEnd(1)) else RmNum(StreamEnd(0));
  | (RmGreaterThan(RmNum(s), e2))      -> let e2' = (eval1S e2) in RmGreaterThan(RmNum(s),e2')
  | (RmGreaterThan(e1, e2))            -> let e1' = (eval1S e1) in RmGreaterThan(e1',e2)

  (* TODO Implement streams properly!*)
  | (RmGreaterEqualTo(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> if n>=m then RmNum(StreamEnd(1)) else RmNum(StreamEnd(0));
  | (RmGreaterEqualTo(RmNum(s), e2))      -> let e2' = (eval1S e2) in RmGreaterEqualTo(RmNum(s),e2')
  | (RmGreaterEqualTo(e1, e2))            -> let e1' = (eval1S e1) in RmGreaterEqualTo(e1',e2)
 
  (* TODO Implement streams properly!*)
  | (RmEqualTo(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> print_string "EQUAL TO IS TOTALLY RUNNING\n"; if n=m then RmNum(StreamEnd(1)) else RmNum(StreamEnd(0));
  | (RmEqualTo(RmNum(s), e2))      -> let e2' = (eval1S e2) in RmEqualTo(RmNum(s),e2')
  | (RmEqualTo(e1, e2))            -> let e1' = (eval1S e1) in RmEqualTo(e1',e2) 

  (* TODO Implement streams properly!*)
  | (RmNotEqualTo(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> if n<>m then RmNum(StreamEnd(1)) else RmNum(StreamEnd(0));
  | (RmNotEqualTo(RmNum(s), e2))      -> let e2' = (eval1S e2) in RmNotEqualTo(RmNum(s),e2')
  | (RmNotEqualTo(e1, e2))            -> let e1' = (eval1S e1) in RmNotEqualTo(e1',e2)

  (* Operators *)
  (* TODO Implement streams properly!*)
  | (RmPlus(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> RmNum(StreamEnd(n+m))
  | (RmPlus(RmNum(Stream(n,_)), e2))      -> let e2' = (eval1S e2) in RmPlus(RmNum(StreamEnd(n)),e2')
  | (RmPlus(e1, e2))            -> let e1' = (eval1S e1) in RmPlus(e1', e2)

  (* TODO Implement streams properly!*)
  | (RmMinus(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> RmNum(StreamEnd(n-m))
  | (RmMinus(RmNum(Stream(n,_)), e2))      -> let e2' = (eval1S e2) in RmMinus(RmNum(StreamEnd(n)),e2')
  | (RmMinus(e1, e2))            -> let e1' = (eval1S e1) in RmMinus(e1', e2)

  (* TODO Implement streams properly!*)
  | (RmMultiply(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> RmNum(StreamEnd(n*m))
  | (RmMultiply(RmNum(Stream(n,_)), e2))      -> let e2' = (eval1S e2) in RmMultiply(RmNum(StreamEnd(n)),e2')
  | (RmMultiply(e1, e2))            -> let e1' = (eval1S e1) in RmMultiply(e1', e2)

  (* TODO Implement streams properly!*)
  | (RmDivide(RmNum(Stream(n,_)),RmNum(Stream(m,_)))) -> RmNum(StreamEnd(n/m))
  | (RmDivide(RmNum(Stream(n,_)), e2))      -> let e2' = (eval1S e2) in RmDivide(RmNum(StreamEnd(n)),e2')
  | (RmDivide(e1, e2))            -> let e1' = (eval1S e1) in RmDivide(e1', e2)

  (* TODO Implement streams properly!*)
  | (RmUMinus(RmNum(Stream(n,_)))) -> RmNum(StreamEnd(-n))
  | (RmUMinus(e1))      -> let e1' = (eval1S e1) in RmUMinus(e1')

  | (RmIf(RmNum(Stream(n,_)),e2,e3))        -> print_string "IF TEST: "; if n = 0 then e3 else e2
  | (RmIf(e1,e2,e3))              -> print_string "IF SIMPLIFY\n"; let e1' = (eval1S e1) in RmIf(e1',e2,e3)

  | (RmLet(tT,x,e1,e2)) when (isValue(e1)) -> subst e1 x e2
  | (RmLet(tT,x,e1,e2))                    -> let e1' = (eval1S e1) in RmLet(tT,x,e1',e2)

  | (RmApp(RmLbd(rT,tT,x,e), e2)) when (isValue(e2)) -> subst e2 x e
  | (RmApp(RmLbd(rT,tT,x,e), e2))                    -> let e2' = (eval1S e2) in RmApp( RmLbd(rT,tT,x,e) , e2')
  | (RmApp(e1,e2))                                -> let e1' = (eval1S e1) in RmApp(e1',e2)

  | _ -> print_string "NO MATCH, RAISING TERMINATED\n";raise Terminated ;;


let rec evalloop e = try ( let e' = eval1S e in evalloop e') with Terminated -> if (isValue e) then e else raise StuckTerm ;;
let evalProg e = evalloop e ;;


let rec type_to_string tT = match tT with
  | RivInt -> "Int"
  | RivFun(tT1,tT2) -> "( "^type_to_string(tT1)^" -> "^type_to_string(tT2)^" )" 
;;

(* FIXME When type checker working make this print out streams *)

let print_res res = match res with
  | RmNum (Stream(i,_)) -> print_int i ; print_string " : Int"
  (* | (RmLbd(rT,tT,x,e)) -> print_string("Function : " ^ type_to_string( typeProg (res) )) *)
  | _ -> raise NonBaseTypeResult
;;
