exception LookupError of string ;;
exception TypeError of string;;
exception UnboundVariableError of string;;
exception Terminated of string;;
exception StuckTerm of string;;
exception NonBaseTypeResult of string;;

open Printf;;

(* Stream implementation *)
type 'a stream = Stream of 'a * (unit -> 'a stream) | StreamEnd of unit;;
let hd : 'a stream -> 'a = function Stream (a, _) -> a;;
let tl : 'a stream -> 'a stream = function Stream (_, s) -> s ();;

(* Types of the language *)
type rivType =  RivUnit | RivInt | RivFun of rivType * rivType | RivStream of rivType

(* Grammar of the language *)
type rivTerm =
  | RmNum of int
  | RmStream of rivType * rivTerm stream
  | RmVar of string
  | RmUnit of unit
  | RmUMinus of rivTerm
  | RmApp of rivTerm * rivTerm
  | RmMinus of rivTerm * rivTerm
  | RmPlus of rivTerm * rivTerm
  | RmMultiply of rivTerm * rivTerm
  | RmDivide of rivTerm * rivTerm 
  | RmLessThan of rivTerm * rivTerm
  | RmLessEqualTo of rivTerm * rivTerm
  | RmGreaterThan of rivTerm * rivTerm
  | RmGreaterEqualTo of rivTerm * rivTerm
  | RmNotEqualTo of rivTerm * rivTerm
  | RmEqualTo of rivTerm * rivTerm
  (* Cons: int * int -> stream<int>*)
  | RmCons of rivTerm  * rivTerm
  (* Append: int * int -> int *)
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
  | RmRead of unit


let rec isValue e = print_string "isValue called\n"; match e with
  | RmNum(s) -> true
  | RmUnit() -> true
  | RmStream(tT,s) -> true
  | RmLbd(rT,tT,x,e') -> true
  | RmLbdEmpty(rT,e') -> true
  | RmRead() -> true
  | _ -> false
;;

(* Type of Environments *)
type 'a context = Env of (string * 'a) list
type typeContext = rivType context
type valContext = rivTerm context

(* Function to look up the type of a string name variable in a type environment *)
let rec lookup env str = match env with
   Env [] -> raise (LookupError "Empty Environment")
  |Env ((name,thing) :: gs) ->
  (
    match (name = str) with
    true -> thing
    |false -> lookup (Env (gs)) str
  )
;;

let rec type_to_string tT = match tT with
  | RivUnit -> "Unit"
  | RivInt -> "Int"
  | RivFun(tT1,tT2) -> "( "^type_to_string(tT1)^" -> "^type_to_string(tT2)^" )"
  | RivStream(tT) -> type_to_string(tT) ^ " stream"
;;

(* Function to add an extra entry in to an environment *)
let addBinding env str thing = match env with
Env(gs) -> Env ( (str, thing) :: gs ) ;;

(* The type checking function itself *) 
let rec typeOf env e = match e with 
   RmUnit () -> RivUnit

  |RmVar (x) ->  (try lookup env x with LookupError _ -> raise (TypeError "Variable"))

  |RmStream (tT, Stream(e,_)) ->
    ( match (typeOf env e) with
        RivInt -> RivInt
      | RivStream(tT) -> RivStream(tT)
      | _ -> raise (TypeError "Stream")
    )
  
  |RmNum (n) -> RivStream(RivInt)

  |RmUMinus (e1) -> 
    ( match (typeOf env e1) with
	RivStream(RivInt) -> RivStream(RivInt)
      | _ -> raise (TypeError "UMinus")
    )

  |RmMinus(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt) 
                    |_ -> raise (TypeError "Minus")
    )

  |RmPlus(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt) 
                    |_ -> raise (TypeError "Plus")
    )

  |RmMultiply(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt) 
                    |_ -> raise (TypeError "Multiply")
    )

  |RmDivide(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt) 
                    |_ -> raise (TypeError "Divide")
    )


  |RmLessThan (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt)
      | _ -> raise (TypeError "Less Than")
    )

  |RmGreaterThan (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt)
      | _ -> raise (TypeError "Greater Than")
    )

  |RmGreaterEqualTo (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt)
      | _ -> raise (TypeError "Greater Equal To")
    )

  |RmLessEqualTo (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt)
      | _ -> raise (TypeError "Less Equal To")
    )

  |RmNotEqualTo (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt)
      | _ -> raise (TypeError "Not Equal To")
    )

  |RmEqualTo (e1,e2) -> 
    ( match (typeOf env e1) , (typeOf env e2) with 
        RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt)
      | _ -> raise (TypeError "Equal To")
    )


  |RmCons(e1,e2) -> 
    (let ty1 = typeOf env e1 in
     let ty2 = typeOf env e2 in
      (if (ty1 = ty2) then
        RivStream(ty1) 
      else
        raise (TypeError "Cons: Types of streams don't match")
      )
    )

  |RmAppend(e1,e2) -> 
    (let ty1 = typeOf env e1 in
     let ty2 = typeOf env e2 in
      (if (ty1 = ty2) then
        ty1
      else
        raise (TypeError "Append: Types of streams don't match")
      )
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
         RivStream(RivInt) -> (
                  let ty1 = typeOf env e2 in 
		  let ty2 = typeOf env e3 in 
		   (match (ty1=ty2) with 
		      true -> ty1 
		     |false -> raise (TypeError "If: Return expressions not of same type")
		   )
	)
       |_ -> raise (TypeError "If:Conditional not of type RivInt") 
  )

  |RmLet (tT, x, e1, e2) -> 
    (
      let ty1 = typeOf env e1 in
      let ty2 = typeOf (addBinding env x tT) e2 in 
         print_string "Letting To be "; print_string (type_to_string ty1); print_string "\n";
         print_string "Defined as type "; print_string (type_to_string tT); print_string "\n";
         (match (ty1 = tT) with 
            true -> ty2
	         |false -> raise (TypeError "Let")
	 )
    )

  |RmApp (e1,e2) -> 
    ( let ty1 = typeOf env e1 in 
      let ty2 = typeOf env e2 in 
       ( 
        match ty1 with
         RivFun(tT,tU) -> 
         print_string "Function: "; print_string (type_to_string ty1); print_string "\n";
         print_string "Function: From "; print_string (type_to_string tT); print_string "\n";
         print_string "Function: To "; print_string (type_to_string tU); print_string "\n";
         print_string "Applying to: "; print_string (type_to_string ty2); print_string "\n";
            (
	     match tT = ty2 with
             true -> tT 
            |false -> raise (TypeError "Apply: Expressions not of same type")
            )
        | _ -> raise (TypeError "Apply: Not of type function")
        )
    )
  |RmRead () -> RivStream(RivStream(RivInt))

  |RmLbd(rT,tT,x,e) ->  RivFun(typeOf (addBinding env x tT) e, rT)
  |RmLbdEmpty (rT,e) ->  RivFun(RivUnit, rT) 
  
	

let typeProg e = typeOf (Env []) e ;;

let rename (s:string) = s^"'";;

let rec convert_to_stream str = 
    let tokens = (Str.split (Str.regexp "[ \t]+") str) in
   	let rec convert s = match s with
      | [] -> StreamEnd()
      | h :: t -> Stream(
        RmNum(int_of_string(h)),
        function () -> convert(t)
      )
    in match tokens with 
    | [] -> StreamEnd()
    | h :: t  -> Stream(RmNum(int_of_string (h)), function () -> convert (t))

let rec read_stream () =
    Stream(RmStream(RivStream(RivInt),
      (try (convert_to_stream(input_line stdin)) with End_of_file -> StreamEnd())),
      function () -> read_stream()
    )

let rec eval1M env e = match e with
  | (RmUnit()) -> print_string "UNIT \n"; raise (Terminated "Unit")
  | (RmVar x) -> print_string "VARIABLE: "; print_string x; print_string "\n"; (try ((lookup env x), env) with LookupError _ -> raise (UnboundVariableError "Variable not bound"))
  | (RmNum n) -> (*print_string "NUMBER: "; print_int n; print_string "\n"; *) raise (Terminated "Number")
  | (RmLbd(rT,tT,y,e')) -> print_string "LAMBDA"; raise (Terminated "Lambda")
  | (RmLbdEmpty(rT,e')) -> print_string "EMPTY LAMBDA"; raise (Terminated "Unit Lambda")

  | (RmStream (tT, Stream(_,_))) -> print_string "terminating on Stream\n"; raise (Terminated "Stream")
  | (RmStream (tT, StreamEnd())) -> print_string "terminating on StreamEnd\n";  raise (Terminated "StreamEnd")

  (* Conditionals *)
  | (RmLessThan(RmNum(n),RmNum(m))) -> ((if n<m then RmNum(1) else RmNum(0)), env)
  | (RmLessThan(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmLessThan(RmNum(n),e2'),env')
  | (RmLessThan(RmStream(tT,n), RmStream(_,m))) -> 
      let rec recurse x y = match (x,y) with 
        | (Stream(a,ae),Stream(b,be)) -> 
           Stream(
            (let (e,_) = (eval1M env (RmLessThan(a,b))) in e),
            function () -> recurse (ae()) (be())
          )
        | (StreamEnd(),_)
        | (_,StreamEnd()) -> StreamEnd()
      in (RmStream(tT, recurse n m), env)
  | (RmLessThan(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmLessThan(RmStream(tT, s),e2'), env')
  | (RmLessThan(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmLessThan(e1',e2),env')

  | (RmLessEqualTo(RmNum(n),RmNum(m))) -> ((if n<=m then RmNum(1) else RmNum(0)), env)
  | (RmLessEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmLessEqualTo(RmNum(n),e2'),env')
  | (RmLessEqualTo(RmStream(tT,n), RmStream(_,m))) -> 
      let rec recurse x y = match (x,y) with 
        | (Stream(a,ae),Stream(b,be)) -> 
           Stream(
            (let (e,_) = (eval1M env (RmLessEqualTo(a,b))) in e),
            function () -> recurse (ae()) (be())
          )
        | (StreamEnd(),_)
        | (_,StreamEnd()) -> StreamEnd()
      in (RmStream(tT, recurse n m), env)
  | (RmLessEqualTo(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmLessEqualTo(RmStream(tT, s),e2'), env')
  | (RmLessEqualTo(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmLessEqualTo(e1',e2),env')

  | (RmGreaterThan(RmNum(n),RmNum(m))) -> ((if n>m then RmNum(1) else RmNum(0)), env)
  | (RmGreaterThan(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmGreaterThan(RmNum(n),e2'),env')
  | (RmGreaterThan(RmStream(tT,n), RmStream(_,m))) -> 
      let rec recurse x y = match (x,y) with 
        | (Stream(a,ae),Stream(b,be)) -> 
           Stream(
            (let (e,_) = (eval1M env (RmGreaterThan(a,b))) in e),
            function () -> recurse (ae()) (be())
          )
        | (StreamEnd(),_)
        | (_,StreamEnd()) -> StreamEnd()
      in (RmStream(tT, recurse n m), env)
  | (RmGreaterThan(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmGreaterThan(RmStream(tT, s),e2'), env')
  | (RmGreaterThan(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmGreaterThan(e1',e2),env')

  | (RmGreaterEqualTo(RmNum(n),RmNum(m))) -> ((if n>m then RmNum(1) else RmNum(0)), env)
  | (RmGreaterEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmGreaterEqualTo(RmNum(n),e2'),env')
  | (RmGreaterEqualTo(RmStream(tT,n), RmStream(_,m))) -> 
    let rec recurse x y = match (x,y) with 
      | (Stream(a,ae),Stream(b,be)) -> 
         Stream(
          (let (e,_) = (eval1M env (RmGreaterEqualTo(a,b))) in e),
          function () -> recurse (ae()) (be())
        )
      | (StreamEnd(),_)
      | (_,StreamEnd()) -> StreamEnd()
    in (RmStream(tT, recurse n m), env)
    | (RmGreaterEqualTo(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmGreaterEqualTo(RmStream(tT, s),e2'), env')
  | (RmGreaterEqualTo(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmGreaterEqualTo(e1',e2),env')

  | (RmEqualTo(RmNum(n),RmNum(m))) -> ((if n=m then RmNum(1) else RmNum(0)), env)
  | (RmEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmEqualTo(RmNum(n),e2'),env')
  | (RmEqualTo(RmStream(tT,n), RmStream(_,m))) -> 
    let rec recurse x y = match (x,y) with 
      | (Stream(a,ae),Stream(b,be)) -> 
         Stream(
          (let (e,_) = (eval1M env (RmEqualTo(a,b))) in e),
          function () -> recurse (ae()) (be())
        )
      | (StreamEnd(),_)
      | (_,StreamEnd()) -> StreamEnd()
    in (RmStream(tT, recurse n m), env)
    | (RmEqualTo(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmEqualTo(RmStream(tT, s),e2'), env')
  | (RmEqualTo(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmEqualTo(e1',e2),env')

  | (RmNotEqualTo(RmNum(n),RmNum(m))) -> ((if n<>m then RmNum(1) else RmNum(0)), env)
  | (RmNotEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmNotEqualTo(RmNum(n),e2'),env')
  | (RmNotEqualTo(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M env (RmNotEqualTo(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmNotEqualTo(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmNotEqualTo(RmStream(tT, s),e2'), env')
  | (RmNotEqualTo(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmNotEqualTo(e1',e2),env')

  (* Constructors *)

  | (RmCons(RmStream(nT,n), RmStream(mT,m))) ->
       (RmStream(RivStream(nT), Stream(RmStream(nT,n), function() -> Stream(RmStream(mT,m))), env)

  (* Operators *)

  | (RmPlus(RmNum(n),RmNum(m))) -> (RmNum(n+m) , env)
  | (RmPlus(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmPlus(RmNum(n),e2'), env')
  | (RmPlus(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M env (RmPlus(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmPlus(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmPlus(RmStream(tT, s),e2'), env')
  | (RmPlus(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmPlus(e1', e2), env')

  (* Minus *)
  | (RmMinus(RmNum(n),RmNum(m))) -> (RmNum(n-m) , env)
  | (RmMinus(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmMinus(RmNum(n),e2'), env')
  | (RmMinus(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M env (RmMinus(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmMinus(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmMinus(RmStream(tT, s),e2'), env')
  | (RmMinus(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmMinus(e1', e2), env')

  (* Multiply *)
  | (RmMultiply(RmNum(n),RmNum(m))) -> (RmNum(n*m) , env)
  | (RmMultiply(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmMultiply(RmNum(n),e2'), env')
  | (RmMultiply(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M env (RmMultiply(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmMultiply(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmMultiply(RmStream(tT, s),e2'), env')  
  | (RmMultiply(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmMultiply(e1', e2), env')

  (* Divide *)
  | (RmDivide(RmNum(n),RmNum(m))) -> (RmNum(n/m) , env)
  | (RmDivide(RmNum(n), e2))      -> let (e2',env') = (eval1M env e2) in (RmDivide(RmNum(n),e2'), env')
  | (RmDivide(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M env (RmDivide(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmDivide(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M env e2) in (RmDivide(RmStream(tT, s),e2'), env')  
  | (RmDivide(e1, e2))            -> let (e1',env') = (eval1M env e1) in (RmDivide(e1', e2), env')

  | (RmUMinus(RmNum(n))) -> (RmNum(-n), env)
  | (RmUMinus(RmStream(tT,n))) -> 
  let rec recurse x = match x with 
    | Stream(a,ae)-> 
       Stream(
        (let (e,_) = (eval1M env (RmUMinus(a))) in e),
        function () -> recurse (ae())
      )
    | StreamEnd() -> StreamEnd()
  in (RmStream(tT, recurse n), env)
  | (RmUMinus(e1))      -> let (e1',env') = (eval1M env e1) in (RmUMinus(e1'), env')

  (* Ternary *)
  | (RmIf(RmNum(0),e1,e2))        -> (e2, env)
  | (RmIf(RmNum(_),e1,e2))        -> (e1, env)
  | (RmIf(RmStream(tT,Stream(n,_)),e1,e2)) -> (RmIf(n,e1,e2), env)
  | (RmIf(b,e1,e2))               -> let (b',env') = (eval1M env b) in (RmIf(b',e1,e2), env')

  | (RmLet(tT,x,e1,e2)) when (isValue(e1)) -> (e2, addBinding env x e1)
  | (RmLet(tT,x,e1,e2))                    -> let (e1', env') = (eval1M (addBinding env x e1) e1) in (RmLet(tT,x,e1',e2), env')

  (* Application *)
  | (RmApp(RmLbd(rT,tT,x,e), e2)) when (isValue(e2)) -> (e, addBinding env x e2)
  | (RmApp(RmLbd(rT,tT,x,e), e2))                    -> let (e2',env') = (eval1M env e2) in (RmApp( RmLbd(rT,tT,x,e) , e2'), env')

  | (RmApp(RmLbdEmpty(rT,e), e2)) when (isValue(e2)) -> (e, env)
  | (RmApp(RmLbdEmpty(rT,e), e2))                    -> let (e2',env') = (eval1M env e2) in (RmApp(RmLbdEmpty(rT,e),e2'), env')

  | (RmApp(e1,e2))                                -> let (e1',env') = (eval1M env e1) in (RmApp(e1',e2), env') 

  | (RmRead()) -> 
      (
      RmStream(
        RivStream(RivStream(RivInt)),
        read_stream()
      ), env)

(*  | _ -> print_string "NO MATCH, RAISING TERMINATED\n";raise (Terminated "No match");;
*)
let rec evalloop env e = try ( let (e',env') = (eval1M env e) in (evalloop env' e')) with Terminated _ -> if (isValue e) then e else raise (StuckTerm "Eval loop stuck on term") ;;

let evalProg e = evalloop (Env[]) e ;;

let rec print_res res = match res with
  | RmNum (i) -> print_int i ; print_string " : Int "
  | RmUnit () -> print_string " Unit"
  | RmStream (tT, Stream(n,e)) -> print_string "["; print_res n; print_string " - "; (match e() with Stream(m,me) -> print_res m | StreamEnd() -> print_string "END"); print_string "] : Stream";
  | RmLbd(rT,tT,x,e) -> print_string("Function : " ^ type_to_string( typeProg (res) ))
  | _ -> raise (NonBaseTypeResult "Not able to output result as string")
;;
