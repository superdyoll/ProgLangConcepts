exception LookupError ;;
exception Terminated ;;

open Printf;;

(* Types of the language *)
type rivType =  RivInt | RivBool | RivFun of rivType * rivType

(* Grammar of the language *)
type rivTerm =
    RmNum of int
  | RmVar of string
  | RmApp of rivTerm * rivTerm
  | RmPlus of rivTerm * rivTerm
  | RmMinus of rivTerm * rivTerm
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
  | RmIndex of rivTerm * rivTerm
  | RmSection of rivTerm * rivTerm * rivTerm
  | RmSectionEnd of rivTerm * rivTerm
  | RmIf of rivTerm * rivTerm * rivTerm
  (* Let: item Type * item Name * Lambda Expression * Expression *)
  | RmLet of rivType * string * rivTerm * rivTerm
  (* Lambda: Return Type * Parameter Type * Parameter Name * Expression *)
  | RmLbd of rivType * rivType * string * rivTerm

let rec isValue e = match e with
  | RmNum(n) -> true
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

  |RmLessEqualTo (e1,e2) ->
  ( match (typeOf env e1) , (typeOf env e2) with
    RivInt, RivInt -> RivBool
    | _ -> raise TypeError
  )

  |RmGreaterEqualTo (e1,e2) ->
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

(* Return True if the variable x is used in e *)
let rec free e x = match e with
  RmVar(y) -> (x=y)
  |RmNum(n) -> false
  |RmIf(t1,t2,t3) -> (free t1 x) || (free t2 x) || (free t3 x)
  |RmLessThan(e1,e2) -> (free e1 x) || (free e2 x)
  |RmLessEqualTo(e1,e2) -> (free e1 x) || (free e2 x)
  |RmGreaterThan(e1,e2) -> (free e1 x) || (free e2 x)
  |RmGreaterEqualTo(e1,e2) -> (free e1 x) || (free e2 x)
  |RmEqualTo(e1,e2) -> (free e1 x) || (free e2 x)
  |RmPlus(e1,e2) -> (free e1 x) || (free e2 x)
  |RmApp(e1,e2) -> (free e1 x) || (free e2 x)
  |RmLbd(rT,tT,y,e1) when (x=y) -> false
  |RmLbd(rT,tT,y,e1)            -> (free e1 x)
  |RmLet(tT,y,e1,e2) when (x=y) -> (free e1 x) 
  |RmLet(tT,y,e1,e2)            -> (free e1 x) || (free e2 x)
;;

let rename (s:string) = s^"'";;

(* Substitute e1 as 'x' in e2 *)
let rec subst e1 x e2 = match e2 with
  RmVar(y) when (x=y) -> e1
  | RmVar(y) -> RmVar(y)
  | RmNum(n) -> RmNum(n)
  (* Substitute all the parameters *)
  | RmIf(b,e21,e22) -> RmIf( (subst e1 x b) , (subst e1 x e21) , (subst e1 x e22) )
  | RmLessThan(e21, e22) -> RmLessThan( (subst e1 x e21) , (subst e1 x e22) )
  | RmPlus(e21, e22) -> RmPlus( (subst e1 x e21) , (subst e1 x e22) )
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
  | (RmVar x) -> raise Terminated
  | (RmNum n) -> raise Terminated
  | (RmLbd(rT,tT,y,e')) -> raise Terminated

  (*FIXME make it return actual less than values *)
  | (RmLessThan(RmNum(n),RmNum(m))) -> print_string "[*"; print_int n; print_string "<"; print_int m; print_string "*]"; if n<m then RmNum(1) else RmNum(0);
  | (RmLessThan(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmLessThan(RmNum(n),e2')
  | (RmLessThan(e1, e2))            -> let e1' = (eval1S e1) in RmLessThan(e1',e2)

  | (RmGreaterThan(RmNum(n),RmNum(m))) -> print_string "[*"; print_int n; print_string ">"; print_int m; print_string "*]"; if n>m then RmNum(1) else RmNum(0);
  | (RmGreaterThan(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmGreaterThan(RmNum(n),e2')
  | (RmGreaterThan(e1, e2))            -> let e1' = (eval1S e1) in RmGreaterThan(e1',e2)

  | (RmLessEqualTo(RmNum(n),RmNum(m))) -> print_string "[*"; print_int n; print_string "<="; print_int m; print_string "*]"; if n<=m then RmNum(1) else RmNum(0);
  | (RmLessEqualTo(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmLessEqualTo(RmNum(n),e2')
  | (RmLessEqualTo(e1, e2))            -> let e1' = (eval1S e1) in RmLessEqualTo(e1',e2)

  | (RmGreaterEqualTo(RmNum(n),RmNum(m))) -> print_string "[*"; print_int n; print_string ">="; print_int m; print_string "*]"; if n>=m then RmNum(1) else RmNum(0);
  | (RmGreaterEqualTo(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmGreaterEqualTo(RmNum(n),e2')
  | (RmGreaterEqualTo(e1, e2))            -> let e1' = (eval1S e1) in RmGreaterEqualTo(e1',e2)

  | (RmPlus(RmNum(n),RmNum(m))) -> print_string "[*"; print_int n; print_string " + "; print_int m; print_string "*]"; RmNum(n+m)
  | (RmPlus(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmPlus(RmNum(n),e2')
  | (RmPlus(e1, e2))            -> let e1' = (eval1S e1) in RmPlus(e1', e2)

  | (RmMinus(RmNum(n),RmNum(m))) -> print_string "[*"; print_int n; print_string " - "; print_int m; print_string "*]"; RmNum(n-m)
  | (RmMinus(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmMinus(RmNum(n),e2')
  | (RmMinus(e1, e2))            -> let e1' = (eval1S e1) in RmMinus(e1', e2)

  | (RmMultiply(RmNum(n),RmNum(m))) -> print_string "[*"; print_int n; print_string " * "; print_int m; print_string "*]"; RmNum(n*m)
  | (RmMultiply(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmMultiply(RmNum(n),e2')
  | (RmMultiply(e1, e2))            -> let e1' = (eval1S e1) in RmMultiply(e1', e2)

  | (RmDivide(RmNum(n),RmNum(m))) -> print_string "[*"; print_int n; print_string " / "; print_int m; print_string "*]"; RmNum(n/m)
  | (RmDivide(RmNum(n), e2))      -> let e2' = (eval1S e2) in RmDivide(RmNum(n),e2')
  | (RmDivide(e1, e2))            -> let e1' = (eval1S e1) in RmDivide(e1', e2)

 (*TODO (Lloyd) MAKE EVERYTHING RETURN VALUES*)

 (* TODO eval A or B (not both) *)
  | (RmIf(RmNum(n),e2,e3))              -> (*print_string "[* if "; print_int n; print_string " == 0 then"; print_int (eval1S e2); print_string "else"; print_int(eval1S e3);*) if n == 0 then (eval1S e2) else (eval1S e3)
  | (RmIf(e1,e2,e3))              -> let e1' = (eval1S e1) in RmIf(e1',e2,e3)

  | (RmLet(tT,x,e1,e2)) when (isValue(e1)) -> print_string "[* let "; print_string x; print_string " be "; (eval1S tT) ; print_string " in "; print_int subst e1 x e2; print_string "*]";
  | (RmLet(tT,x,e1,e2))                    -> let e1' = (eval1S e1) in RmLet(tT,x,e1',e2)

  | (RmApp(RmLbd(rT,tT,x,e), e2)) when (isValue(e2)) -> print_string "[* Call: Substitute "; print_string tT; print_string " with "; print_int e;  print_int subst e2 x e
  | (RmApp(RmLbd(rT,tT,x,e), e2))                    -> let e2' = (eval1S e2) in RmApp( RmLbd(rT,tT,x,e) , e2')
  | (RmApp(e1,e2))                                -> let e1' = (eval1S e1) in RmApp(e1',e2) 

  | _ -> raise Terminated ;;


let rec evalloop e = try ( let e' = eval1S e in evalloop e') with Terminated -> if (isValue e) then e else raise StuckTerm ;;
let evalProg e = evalloop e ;;


let rec type_to_string tT = match tT with
  | RivInt -> "Int"
  | RivFun(tT1,tT2) -> "( "^type_to_string(tT1)^" -> "^type_to_string(tT2)^" )" 
;;

let print_res res = match res with
  | (RmNum i) -> print_int i ; print_string " : Int"
  | (RmLbd(rT,tT,x,e)) -> print_string("Function : "^type_to_string( typeProg (res) ))
  | _ -> raise NonBaseTypeResult
;;
