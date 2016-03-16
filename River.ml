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
    RmNum of int
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

(* The type checking function itself *) 
let rec typeOf env e = match e with 
   RmNum (n) -> RivInt

  |RmVar (x) ->  (try lookup env x with LookupError -> raise TypeError)

  |RmUMinus (e1) -> 
    ( match (typeOf env e1) with
	RivInt -> RivInt
      | _ -> raise TypeError
    )

  |RmMinus(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivInt, RivInt -> RivInt 
                    |_ -> raise TypeError
    )

  |RmPlus(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivInt, RivInt -> RivInt 
                    |_ -> raise TypeError
    )

  |RmMultiply(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivInt, RivInt -> RivInt 
                    |_ -> raise TypeError
    )

  |RmDivide(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivInt, RivInt -> RivInt 
                    |_ -> raise TypeError
    )


  |RmLessThan (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivInt, RivInt -> RivInt
      | _ -> raise TypeError
    )

  |RmGreaterThan (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivInt, RivInt -> RivInt

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

let rec eval1M env e = match e with
  | (RmVar x) -> print_string "VARIABLE: "; print_string x; print_string "\n"; (try ((lookup env x), env) with LookupError -> raise UnboundVariableError)
  | (RmNum n) -> print_string "NUMBER: "; print_int n; print_string "\n"; raise Terminated
  | (RmLbd(rT,tT,y,e')) -> raise Terminated

  (* Conditionals *)
  | (RmLessThan(RmNum(n),RmNum(m))) -> ((if n<m then RmNum(1) else RmNum(0)), env)
  | (RmLessThan(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmLessThan(RmNum(n),e2'),env')
  | (RmLessThan(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmLessThan(e1',e2),env')

  | (RmLessEqualTo(RmNum(n),RmNum(m))) -> ((if n<=m then RmNum(1) else RmNum(0)), env)
  | (RmLessEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmLessEqualTo(RmNum(n),e2'),env')
  | (RmLessEqualTo(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmLessEqualTo(e1',e2),env')

  | (RmGreaterThan(RmNum(n),RmNum(m))) -> ((if n>m then RmNum(1) else RmNum(0)), env)
  | (RmGreaterThan(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmGreaterThan(RmNum(n),e2'),env')
  | (RmGreaterThan(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmGreaterThan(e1',e2),env')

  | (RmGreaterEqualTo(RmNum(n),RmNum(m))) -> ((if n>m then RmNum(1) else RmNum(0)), env)
  | (RmGreaterEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmGreaterEqualTo(RmNum(n),e2'),env')
  | (RmGreaterEqualTo(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmGreaterEqualTo(e1',e2),env')

  | (RmEqualTo(RmNum(n),RmNum(m))) -> ((if n=m then RmNum(1) else RmNum(0)), env)
  | (RmEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmEqualTo(RmNum(n),e2'),env')
  | (RmEqualTo(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmEqualTo(e1',e2),env')

  | (RmNotEqualTo(RmNum(n),RmNum(m))) -> ((if n<>m then RmNum(1) else RmNum(0)), env)
  | (RmNotEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmNotEqualTo(RmNum(n),e2'),env')
  | (RmNotEqualTo(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmNotEqualTo(e1',e2),env')

  (* Operators *)
  | (RmPlus(RmNum(n),RmNum(m))) -> (RmNum(n+m) , env)
  | (RmPlus(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmPlus(RmNum(n),e2'), env')
  | (RmPlus(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmPlus(e1', e2), env')

  | (RmMinus(RmNum(n),RmNum(m))) -> (RmNum(n-m) , env)
  | (RmMinus(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmMinus(RmNum(n),e2'), env')
  | (RmMinus(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmMinus(e1', e2), env')

  | (RmMultiply(RmNum(n),RmNum(m))) -> (RmNum(n*m) , env)
  | (RmMultiply(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmMultiply(RmNum(n),e2'), env')
  | (RmMultiply(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmMultiply(e1', e2), env')

  | (RmDivide(RmNum(n),RmNum(m))) -> (RmNum(n/m) , env)
  | (RmDivide(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmDivide(RmNum(n),e2'), env')
  | (RmDivide(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmDivide(e1', e2), env')

  | (RmUMinus(RmNum(n))) -> (RmNum(-n), env)
  | (RmUMinus(e1))      -> let (e1',env') = (eval1M env e1) in (RmUMinus(e1'), env')

  (* Tenary *)
  | (RmIf(RmNum(1),e1,e2))        -> (e1, env)
  | (RmIf(RmNum(0),e1,e2))        -> (e2, env)
  | (RmIf(b,e1,e2))               -> let (b',env') = (eval1M env b) in (RmIf(b',e1,e2), env')

  | (RmLet(tT,x,e1,e2)) when (isValue(e1)) -> (e2, addBinding env x e1)
  | (RmLet(tT,x,e1,e2))                    -> let (e1', env') = (eval1M env e1) in (RmLet(tT,x,e1',e2), env')

  | (RmApp(RmLbd(rT,tT,x,e), e2)) when (isValue(e2)) -> (e, addBinding env x e2)
  | (RmApp(RmLbd(rT,tT,x,e), e2))                    -> let (e2',env') = (eval1M env e2) in (RmApp( RmLbd(rT,tT,x,e) , e2'), env')
  | (RmApp(e1,e2))                                -> let (e1',env') = (eval1M env e1) in (RmApp(e1',e2), env') 

  | _ -> print_string "NO MATCH, RAISING TERMINATED\n";raise Terminated ;;


let rec evalloop env e = try ( let (e',env') = (eval1M env e) in (evalloop env' e')) with Terminated -> if (isValue e) then e else raise StuckTerm ;;
let evalProg e = evalloop (Env[]) e ;;


let rec type_to_string tT = match tT with
  | RivInt -> "Int"
  | RivFun(tT1,tT2) -> "( "^type_to_string(tT1)^" -> "^type_to_string(tT2)^" )" 
;;

(* FIXME When type checker working make this print out streams *)

let print_res res = match res with
  | RmNum (i) -> print_int i ; print_string " : Int"
  (* | (RmLbd(rT,tT,x,e)) -> print_string("Function : " ^ type_to_string( typeProg (res) )) *)
  | _ -> raise NonBaseTypeResult
;;
