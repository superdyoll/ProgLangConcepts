(* Exceptions
exception LookupError ;;
*)

open Printf;;

(* Types of the language *)
type rivType =  RivInt | RivBool | RivFun of rivType * rivType

(* Grammar of the language *)
type rivTerm =
    RmNum of int
  | RmVar of string
  (* TODO:  maybe make the below a tuple? Benefit of doing so?*)
  | RmLet of  [string * rivTerm] * rivTerm
  | RmApp of  rivTerm * rivTerm
  | RmPlus of  rivTerm * rivTerm
  | RmMinus of  rivTerm * rivTerm
  | RmMultiply of  rivTerm * rivTerm
  | RmDivide of  rivTerm * rivTerm 
  | RmLessThan of  rivTerm * rivTerm
  | RmGreaterThan of  rivTerm * rivTerm
  | RmGreaterEqualTo of  rivTerm * rivTerm
  | RmLessEqualTo of  rivTerm * rivTerm
  | RmNotEqualTo of  rivTerm * rivTerm
  | RmEqualTo of  rivTerm * rivTerm
  | RmCons of  rivTerm  * rivTerm
  | RmAppend of rivTerm * rivTerm
  | RmIndex of rivTerm * rivTerm
  | RmSection of rivTerm * rivTerm * rivTerm
  | RmSectionEnd of rivTerm * rivTerm
  | RmSection of rivTerm * rivTerm * rivTerm


let rec isValue e = match e with
  | RmNum(n) -> true
  | RmAbs(x,tT,e') -> true
  | _ -> false
;;

(* Type of Environments *)

type 'a context = Env of (string * 'a) list
type typeContext = rivType context
type valContext = rivTerm context

(* Function to look up the type of a string name variable in a type environment *)
let rec lookup env str = match env with
  |Env [] -> raise LookupError
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

(* TODO: Type Checker *)
(* (* The type checking function itself *)
let rec typeOf env e = match e with
  RmNum (n) -> RivInt

  |RmLessThan (e1,e2) ->
  ( match (typeOf env e1) , (typeOf env e2) with
    RivInt, RivInt -> RivBool
    | _ -> raise TypeError
  )

  |RmGreaterThan (e1,e2) ->
  ( match (typeOf env e1) , (typeOf env e2) with
    RivInt, RivInt -> RivBool
    | _ -> raise TypeError
  )

  |RmLessThanEqualTo (e1,e2) ->
  ( match (typeOf env e1) , (typeOf env e2) with
    RivInt, RivInt -> RivBool
    | _ -> raise TypeError
  )

  |RmGreaterThanEqualTo (e1,e2) ->
  ( match (typeOf env e1) , (typeOf env e2) with
    RivInt, RivInt -> RivBool
    | _ -> raise TypeError
  )

  |RmEqualTo (e1,e2) ->
  ( match (typeOf env e1) , (typeOf env e2) with
    RivInt, RivInt -> RivBool
    | _ -> raise TypeError
  )

  |RmPlus(e1,e2) ->
  (
   match (typeOf env e1) , (typeOf env e2) with
   RivInt, RivInt -> RivInt
   |_ -> raise TypeError
  )

  |RmMinus(e1,e2) ->
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

  |RmVar (x) ->  (try lookup env x with LookupError -> raise TypeError)

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

  |RmLet (x, tT, e1, e2) ->
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

  |RmLambda (x,tT,e) ->  RivFun(tT, typeOf (addBinding env x tT) e)
 
let typeProg e = typeOf (Env []) e ;;
*)
(* End of type Checker *)

(* Checks if a name is free *)
let rec free e x = match e with
  RmVar(y) -> (x=y)
  |RmNum(n) -> false
  |RmBool(b) -> false
  |RmIf(t1,t2,t3) -> (free t1 x) || (free t2 x) || (free t3 x)
  |RmLessThan(e1,e2) -> (free e1 x) || (free e2 x)
  |RmPlus(e1,e2) -> (free e1 x) || (free e2 x)
  |RmApp(e1,e2) -> (free e1 x) || (free e2 x)
  |RmAbs(y,tT,e1) when (x=y) -> false
  |RmAbs(y,tT,e1)            -> (free e1 x)
  |RmLet(y,tT,e1,e2) when (x=y) -> (free e1 x)
  |RmLet(y,tT,e1,e2)            -> (free e1 x) || (free e2 x)
;;

let rename (s:string) = s^"'";;

let rec subst e1 x e2 = match e2 with
  RmVar(y) when (x=y) -> e1
  | RmVar(y)            -> RmVar(y)
  | RmNum(n) -> RmNum(n)
  | RmBool(b) -> RmBool(b)
  | RmIf(b,e21,e22) -> RmIf( (subst e1 x b) , (subst e1 x e21) , (subst e1 x e22) )
  | RmLessThan (e21, e22) -> RmLessThan( (subst e1 x e21) , (subst e1 x e22) )
  | RmPlus(e21, e22) -> RmPlus( (subst e1 x e21) , (subst e1 x e22) )
  | RmApp(e21, e22) -> RmApp( (subst e1 x e21) , (subst e1 x e22) )
  | RmAbs(y,tT,e21) when (x=y) -> RmAbs(y,tT,e21)
  | RmAbs(y,tT,e21) when (not (free e1 y)) -> RmAbs(y,tT,subst e1 x e21)
  | RmAbs(y,tT,e21) when (free e1 y) -> let yy = rename y in subst e1 x (RmAbs(yy,tT, (subst (RmVar(yy)) y e21)))
  | RmLet(y,tT,e21,e22) when (x=y) -> RmLet(y,tT,e21,e22)
  | RmLet(y,tT,e21,e22) when (not(free e1 y)) -> RmLet(y,tT, subst e1 x e21 , subst e1 x e22)
  | RmLet(y,tT,e21,e22) when ((free e1 y)) -> let yy = rename y in subst e1 x ( RmLet(yy, tT, subst (RmVar(yy)) y e21 , subst (RmVar(yy)) y e22) )
;;

let rec eval1S e = match e with
  | (RmVar x) -> raise Terminated
  | (RmNum n) -> raise Terminated
  | (RmBool b) -> raise Terminated
  | (RmAbs(x,tT,e')) -> raise Terminated

  | (RmLessThan(RmNum(n),RmNum(m))) -> RmBool( n < m )
  | (RmLessThan(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmLessThan(RmNum(n),e2')
  | (RmLessThan(e1, e2))            -> let e1' = (eval1S e1) in RmLessThan(e1',e2)

  | (RmPlus(RmNum(n),RmNum(m))) -> RmNum( n + m )
  | (RmPlus(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmPlus(RmNum(n),e2')
  | (RmPlus(e1, e2))            -> let e1' = (eval1S e1) in RmPlus(e1', e2)

  | (RmIf(RmBool(true),e1,e2))    -> e1
  | (RmIf(RmBool(false),e1,e2))   -> e2
  | (RmIf(b,e1,e2))               -> let b' = (eval1S b) in RmIf(b',e1,e2)

  | (RmLet(x,tT,e1,e2)) when (isValue(e1)) ->  subst e1 x e2
  | (RmLet(x,tT,e1,e2))                    -> let e1' = (eval1S e1) in RmLet(x,tT,e1',e2)

  | (RmApp(RmAbs(x,tT,e), e2)) when (isValue(e2)) -> subst e2 x e
  | (RmApp(RmAbs(x,tT,e), e2))                    -> let e2' = (eval1S e2) in RmApp( RmAbs(x,tT,e) , e2')
  | (RmApp(e1,e2))                                -> let e1' = (eval1S e1) in RmApp(e1',e2)

  | _ -> raise Terminated ;;


let rec evalloop e = try ( let e' = eval1S e in evalloop e') with Terminated -> if (isValue e) then e else raise StuckTerm ;;
let evalProg e = evalloop e ;;


let rec type_to_string tT = match tT with
  | RivInt -> "Int"
  (* TODO: Functions) (* | RivFun(tT1,tT2) -> "( "^type_to_string(tT1)^" -> "^type_to_string(tT2)^" )" *)
;;

let print_res res = match res with
  | (RmNum i) -> print_int i ; print_string " : Int"
  | (RmBool b) -> print_string (if b then "true" else "false") ; print_string " : Bool"
  | (RmAbs(x,tT,e)) -> print_string("Function : "^type_to_string( typeProg (res) ))
  | _ -> raise NonBaseTypeResult
;;