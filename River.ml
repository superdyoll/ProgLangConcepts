exception LookupError ;;
exception TypeError ;;
exception UnboundVariableError;;
exception Terminated ;;
exception StuckTerm ;;
exception NonBaseTypeResult;;

open Printf;;

(* Stream implementation *)
type 'a stream = Stream of 'a * (unit -> 'a stream) | StreamEnd;;
let hd : 'a stream -> 'a = function Stream (a, _) -> a;;
let tl : 'a stream -> 'a stream = function Stream (_, s) -> s ();;


(* Types of the language *)
type rivType =  RivUnit | RivInt | RivBool | RivFun of rivType * rivType | RivStream of rivType

(* Grammar of the language *)
type rivTerm =
  | RmNum of int
  | RmStream of rivTerm stream
  | RmVar of string
  | RmUnit of unit
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
  (* Empty Lambda: Return Type * Expression *)
  | RmLbdEmpty of rivType * rivTerm

let rec isValue e = print_string "isValue called\n"; match e with
  | RmNum(s) -> true
  | RmUnit() -> true
  | RmLbd(rT,tT,x,e') -> true
  | RmLbdEmpty(rT,e') -> true
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
   RmUnit () -> RivUnit

  |RmNum (n) -> RivInt

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
      | _ -> raise TypeError
    )

  |RmGreaterEqualTo (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivInt, RivInt -> RivInt
      | _ -> raise TypeError
    )

  |RmLessEqualTo (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivInt, RivInt -> RivBool
      | _ -> raise TypeError
    )

  |RmNotEqualTo (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivInt, RivInt -> RivBool
      | _ -> raise TypeError
    )

  |RmEqualTo (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivInt, RivInt -> RivBool
      | _ -> raise TypeError
    )


  |RmCons(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivInt, RivInt -> RivInt 
                    |_ -> raise TypeError
    )

  |RmAppend(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivInt, RivInt -> RivInt 
                    |_ -> raise TypeError
    )

(*
  |RmIndex(e1,e2) -> 
    ( let ty1 = typeOf env e1 in
      let ty2 = typeOf env e2 in
             match ty1 with RivInt
, RivInt -> RivInt 
                    |_ -> raise TypeError
    )
*)
  |RmIf (e1,e2,e3) -> (
    let ty1 = typeOf env e1 in 
      match ty1 with 
         RivBool -> (
                  let ty1 = typeOf env e2 in 
		  let ty2 = typeOf env e3 in 
		   (match (ty1=ty2) with 
		      true -> ty1 
		     |false -> raise TypeError 
		   )
	)
       |_ -> raise TypeError 
  )

  |RmLet (tT, x, e1, e2) -> 
    (
      let ty1 = typeOf env e1 in
      let ty2 = typeOf (addBinding env x tT) e2 in 
         (match (ty1 = tT) with 
            true -> ty2
	         |false -> raise TypeError
	 )
    )

  |RmApp (e1,e2) -> 
    ( let ty1 = typeOf env e1 in 
      let ty2 = typeOf env e2 in 
       ( 
        match ty1 with 
         RivFun(tT,tU) ->  
            (
	     match tT = ty2 with
             true -> tT 
            |false -> raise TypeError
	    )
	| _ -> raise TypeError 
       )
    )

  |RmLbd (rT,tT,x,e) ->  RivFun(rT, typeOf (addBinding env x tT) e)
  |RmLbdEmpty (rT,e) ->  RivFun(rT, typeOf env e) 

let typeProg e = typeOf (Env []) e ;;

let rename (s:string) = s^"'";;

let rec eval1M env e = match e with
  | (RmUnit()) -> print_string "UNIT \n"; raise Terminated
  | (RmVar x) -> print_string "VARIABLE: "; print_string x; print_string "\n"; (try ((lookup env x), env) with LookupError -> raise UnboundVariableError)
  | (RmNum n) -> print_string "NUMBER: "; print_int n; print_string "\n"; raise Terminated
  | (RmLbd(rT,tT,y,e')) -> print_string "LAMBDA"; raise Terminated
  | (RmLbdEmpty(rT,e')) -> print_string "EMPTY LAMBDA"; raise Terminated

  (* If we're evaluating a stream, return its first value as a number *)
  | (RmStream Stream(n,_)) -> print_string "Parsing stream"; (n, env)
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

  (* Ternary *)
  | (RmIf(RmNum(1),e1,e2))        -> (e1, env)
  | (RmIf(RmNum(0),e1,e2))        -> (e2, env)
  | (RmIf(b,e1,e2))               -> let (b',env') = (eval1M env b) in (RmIf(b',e1,e2), env')

  | (RmLet(tT,x,e1,e2)) when (isValue(e1)) -> (e2, addBinding env x e1)
  | (RmLet(tT,x,e1,e2))                    -> let (e1', env') = (eval1M (addBinding env x e1) e1) in (RmLet(tT,x,e1',e2), env')

  (* Application *)
  | (RmApp(RmLbd(rT,tT,x,e), e2)) when (isValue(e2)) -> (e, addBinding env x e2)
  | (RmApp(RmLbd(rT,tT,x,e), e2))                    -> let (e2',env') = (eval1M env e2) in (RmApp( RmLbd(rT,tT,x,e) , e2'), env')

  | (RmApp(RmLbdEmpty(rT,e), e2)) when (isValue(e2)) -> (e, env)
  | (RmApp(RmLbdEmpty(rT,e), e2))                    -> let (e2',env') = (eval1M env e2) in (RmApp(RmLbdEmpty(rT,e),e2'), env')

  | (RmApp(e1,e2))                                -> let (e1',env') = (eval1M env e1) in (RmApp(e1',e2), env') 

  | _ -> print_string "NO MATCH, RAISING TERMINATED\n";raise Terminated ;;


let rec evalloop env e = try ( let (e',env') = (eval1M env e) in (evalloop env' e')) with Terminated -> if (isValue e) then e else raise StuckTerm ;;
let evalProg e = evalloop (Env[]) e ;;


let rec type_to_string tT = match tT with
  | RivUnit -> "Unit"
  | RivInt -> "Int"
  | RivFun(tT1,tT2) -> "( "^type_to_string(tT1)^" -> "^type_to_string(tT2)^" )" 
;;

(* FIXME When type checker working make this print out streams *)

let print_res res = match res with
  | RmNum (i) -> print_int i ; print_string " : Int"
  | RmUnit () -> print_string " Unit"
  (* | (RmLbd(rT,tT,x,e)) -> print_string("Function : " ^ type_to_string( typeProg (res) )) *)
  | _ -> raise NonBaseTypeResult
;;
