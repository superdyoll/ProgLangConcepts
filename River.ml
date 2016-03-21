exception LookupError of string ;;
exception TypeError of string;;
exception RuntimeError of string;;
exception UnboundVariableError of string;;
exception Terminated of string;;
exception StuckTerm of string;;
exception NonBaseTypeResult of string;;
exception DimensionError of string;;
exception TransposeError of string;;

open Printf;;

(* Stream implementation *)
type 'a stream = Stream of 'a * (unit -> 'a stream) | StreamEnd of unit;;
let hd : 'a stream -> 'a = function Stream (a, _) -> a | StreamEnd() -> StreamEnd();;
let tl : 'a stream -> 'a stream = function Stream (_, s) -> s () | StreamEnd() -> StreamEnd();;

(* Types of the language *)
type rivType =  RivInt | RivFun of rivType * rivType | RivStream of rivType

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
  | RmModulus of rivTerm * rivTerm 
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
  | RmIndex of rivTerm * rivTerm
  | RmSection of rivTerm * rivTerm * rivTerm
  | RmSectionStart of rivTerm * rivTerm
  | RmSectionEnd of rivTerm * rivTerm
  | RmIf of rivTerm * rivTerm * rivTerm
  (* Let: item Type * item Name * Expression for the item * Expression *)
  | RmLet of rivType * string * rivTerm * rivTerm
  (* Lambda: Return Type * Parameter Type * Parameter Name * Expression *)
  | RmLbd of rivType * rivType * string * rivTerm
  (* Empty Lambda: Return Type * Expression *)
  | RmLbdEmpty of rivType * rivTerm
  | RmRead of unit

let rec type_to_string tT = match tT with
  | RivInt -> "Int"
  | RivFun(tT1,tT2) -> "( "^type_to_string(tT1)^" -> "^type_to_string(tT2)^" )"
  | RivStream(tT) -> type_to_string(tT) ^ " stream"
;;

let rec isValue e = 
 match e with
  | RmNum(n) -> true
  (* Type, String *)
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


(* Function to add an extra entry in to an environment *)
let addBinding env str thing = match env with
   Env(gs) -> Env ((str,thing) :: gs) ;;

(* The type checking function itself *) 
let rec typeOf env e = match e with 
  |RmUnit () -> RivStream(RivInt)

  |RmVar (x) ->  (try lookup env x with LookupError _ -> raise (TypeError "Variable"))

  |RmStream(tT, StreamEnd _) -> RivStream(tT)
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
                   | RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt) 
                   |a,b ->
                    raise (TypeError "Plus")
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

  |RmModulus(e1,e2) -> 
    (
     match (typeOf env e1) , (typeOf env e2) with 
             RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt) 
                    |_ -> raise (TypeError "Modulus")
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
        (if (ty1 = RivStream(ty2)) then
          RivStream(ty1)
        else
          raise (TypeError "Cons: Types of streams don't match"))
      )
    )

  |RmAppend(e1,e2) -> 
    (let ty1 = typeOf env e1 in
     let ty2 = typeOf env e2 in
      (if (ty1 = ty2) then
        ty1
      else
        raise (TypeError ("Append: Types of streams don't match, Trying to append type '"^(type_to_string ty1)^"' to type '"^(type_to_string ty2)))
      )
    )


  |RmIndex(e1,e2) -> 
    ( let ty1 = typeOf env e1 in
      let ty2 = typeOf env e2 in
             match (ty2,ty1) with
              | RivStream(RivInt), RivStream(RivInt) -> RivStream(RivInt) 
              | RivStream(RivInt), RivStream(s) -> s
              | RivStream(RivInt), _ -> raise (TypeError "You can only index a stream")
              | _,_ -> raise (TypeError "Index")
    )

  |RmSectionStart(e1,e2) -> 
    ( let ty1 = typeOf env e1 in
      let ty2 = typeOf env e2 in
             match ty2 with 
              | RivStream(RivInt) -> ty1
              |_ -> raise (TypeError "SectionStart")
    )


  |RmSectionEnd(e1,e2) -> 
    ( let ty1 = typeOf env e1 in
      let ty2 = typeOf env e2 in
             match ty2 with 
              | RivStream(RivInt) -> ty1
              |_ -> raise (TypeError "SectionEnd")
    )

  |RmSection(e1,e2,e3) -> 
      ( let ty1 = typeOf env e1 in
        let ty2 = typeOf env e2 in
        let ty3 = typeOf env e3 in
               match ty2, ty3 with 
                | (RivStream(RivInt),RivStream(RivInt)) -> ty1
                | (_,_) -> raise (TypeError "Section")
      )


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
      let ty1 = typeOf (addBinding env x tT) e1 in
      let ty2 = typeOf (addBinding env x tT) e2 in 
        (* Debug Code *)
        (* print_string "Letting To be "; print_string (type_to_string ty1);print_string "\n"; 
        print_string "Defined as type "; print_string (type_to_string tT); print_string "\n";  *)
        (* /Debug Code *)
        (match (ty1 = tT) with 
          |true -> ty2
          (* Todo, make this more informative *)
          |false -> raise (TypeError "Let: Type error")
	 )
    )

  |RmApp (e1,e2) -> 
    ( let ty1 = typeOf env e1 in 
      let ty2 = typeOf env e2 in 
       ( 
        match ty1 with
         RivFun(tT,tU) -> 
         (* Debug Code *)
         (* print_string "Function: "; print_string (type_to_string ty1); print_string "\n";
         print_string "Function: From "; print_string (type_to_string tT); print_string "\n";
         print_string "Function: To "; print_string (type_to_string tU); print_string "\n";
         print_string "Applying to: "; print_string (type_to_string ty2); print_string "\n"; *)
         (* / Debug Code *)
            (
       match tT = ty2 with
             true -> tU
            |false -> raise (TypeError "Apply: Expressions not of same type")
            )
        | _ -> raise (TypeError ("Apply: Not of type function, type is " ^ (type_to_string ty1)))
        )
    )
  |RmRead () -> RivStream(RivStream(RivInt))

  |RmLbd(rT,tT,x,e) -> 
    (* Debug Code *)
    (* print_string ("\n Building Lambda:\n "^x^": "^(type_to_string tT)^"-L>"^(type_to_string rT)^"\n"); *)
    (* / Debug Code *)
    RivFun(tT, rT)
  |RmLbdEmpty (rT,e) ->  RivFun(RivStream(RivInt), rT)

let typeProg e = typeOf (Env []) e ;;

(* This print function is only used for debugging to get a better idea of the layout of streams *)
let rec printStream stream = match stream with
  | Stream(n,e) -> print_res_old n; print_string ", "; printStream (e())
  | StreamEnd() -> print_string "() : StreamEnd"
and print_res_old res = match res with
  | RmNum (i) -> print_int i ; print_string " : Int"
  | RmUnit () -> print_string " Unit"
  | RmStream (tT, Stream(n,e)) ->print_string "["; printStream(Stream(n,e)); print_string "] : Stream";
  | RmStream (tT, StreamEnd()) ->print_string "[] : Stream";
  | RmLbd(rT,tT,x,e) -> print_string("Function : " ^ type_to_string( typeProg (res) ))
  | _ -> raise (NonBaseTypeResult "Not able to output result as string")

let rec shave_first_elements streams =
    match streams with
    |  Stream(RmStream(tT,stream), nextStream) -> (
        (* Match the sub-stream *)
        match stream with
        | Stream(n,ns) -> 
            Stream(n,function () -> (shave_first_elements (nextStream())))
        | StreamEnd() -> 
          (shave_first_elements (nextStream()))
    )
    |  StreamEnd() -> StreamEnd()
    | _ -> raise (TransposeError "Cannot shave first element")

let rec drop_first_elements streams =
    match streams with
    |  Stream(RmStream(tT,stream), nextStream) -> (
        (* Match the sub-stream *)
        match stream with
        | Stream(n,ns) ->
          let chopStream () = RmStream(tT,(ns())) in
            Stream((chopStream()),function () -> (drop_first_elements (nextStream())))
        | StreamEnd() -> 
          (drop_first_elements (nextStream()))
    )
    |  StreamEnd() -> StreamEnd()
    | _ -> raise (TransposeError "Cannot drop first element")

(* Helper function that transposes a stream *)
let rec transpose streams = 
    match streams with
    |  Stream(RmStream(tT,stream),nextStream) -> (
        let (chopped_streams, new_stream) = ((drop_first_elements streams),(shave_first_elements streams)) in
          (Stream(RmStream(tT,new_stream), function () -> (transpose chopped_streams)))
    )
    | Stream(_,_) -> (raise (TransposeError "Cannot Transpose a 1D stream"))
    |  StreamEnd() -> (StreamEnd())

let rename (s:string) = s^"'";;

let rec convertLineToStream tokens = 
    match tokens with 
    | [] -> StreamEnd()
    | h :: t -> (* (print_string ("Putting into Sub-stream "^h^"\n")); *) Stream(
        RmNum(int_of_string(h)),
        function () -> convertLineToStream(t)
      )
;;

(* Helper functions for indexing *)
let rec followNSteps stream steps = 
  if steps > 0 then (
    match stream with
    | Stream(_,x) -> followNSteps (x()) (steps - 1)
    | StreamEnd() -> StreamEnd()
  )
  else stream

let rec endAtN stream steps = 
  if steps > 0 then (
    match stream with
    | Stream(n,x) -> Stream(n,function () -> (endAtN (x()) (steps - 1)))
    | StreamEnd() -> StreamEnd()
  )
  else StreamEnd()
  (* End of Helper functions for indexing *)

let rec convertToStream strList = 
  match strList with
  | [] -> StreamEnd()
  | h :: [] -> 
  let tokens = (Str.split (Str.regexp "[ \t]+") h) in 
    Stream( RmStream(RivStream(RivInt), convertLineToStream(tokens)),function () -> StreamEnd())
  | h :: t -> (* (print_string ("Putting into Stream "^h^"\n")); *)
  let tokens = (Str.split (Str.regexp "[ \t]+") h) in 
    Stream( RmStream(RivStream(RivInt), convertLineToStream(tokens)),function () -> convertToStream(t))
;;

let rec eval1M inStreams env e = match e with
  | (RmUnit()) -> (RmStream(RivInt, StreamEnd()), env)
  | (RmVar x) -> (try ((lookup env x), env) with LookupError _ -> raise (UnboundVariableError ("Variable '"^x^"' not bound")))
  | (RmNum n) -> (RmStream(RivInt, Stream(RmNum (n),function () -> StreamEnd())), env)
  | (RmLbd(rT,tT,y,e')) -> raise (Terminated "Lambda")
  | (RmLbdEmpty(rT,e')) -> raise (Terminated "Unit Lambda")

  | (RmStream (tT, Stream(_,_))) -> 
   raise (Terminated "Stream")
  | (RmStream (tT, StreamEnd())) ->
   raise (Terminated "StreamEnd")

  (* ==Conditionals== *)
  (* Less Than *)
  | (RmLessThan(RmNum(n),RmNum(m))) -> ((if n<m then RmNum(1) else RmNum(0)), env)
  | (RmLessThan(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmLessThan(RmNum(n),e2'),env')
  | (RmLessThan(RmStream(tT,n), RmStream(_,m))) -> 
      let rec recurse x y = match (x,y) with 
        | (Stream(a,ae),Stream(b,be)) -> 
           Stream(
            (let (e,_) = (eval1M inStreams env (RmLessThan(a,b))) in e),
            function () -> recurse (ae()) (be())
          )
        | (StreamEnd(),_)
        | (_,StreamEnd()) -> StreamEnd()
      in (RmStream(tT, recurse n m), env)
  | (RmLessThan(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams  env e2) in (RmLessThan(RmStream(tT, s),e2'), env')
  | (RmLessThan(e1, e2))            -> let (e1',env') = (eval1M inStreams  env e1) in (RmLessThan(e1',e2),env')

  (* Less Equal *)
  | (RmLessEqualTo(RmUnit(),RmUnit())) -> (RmNum(1),env)
  | (RmLessEqualTo(RmUnit(),e2))        ->
      (match e2 with 
          RmStream(tT,StreamEnd()) -> (RmNum(1),env)
        | RmStream(_,_) -> (RmNum(0),env)
        | _ -> let (e2',env') = (eval1M inStreams env e2)
               in (RmLessEqualTo(e2',RmUnit()), env)
      )
  | (RmLessEqualTo(e1,RmUnit()))        ->
      (match e1 with 
          RmStream(tT,StreamEnd()) -> (RmNum(1),env)
        | RmStream(_,_) -> (RmNum(0),env)
        | _ -> let (e1',env') = (eval1M inStreams env e1)
               in (RmLessEqualTo(e1',RmUnit()), env)
      )
  | (RmLessEqualTo(RmNum(n),RmNum(m))) -> ((if n<=m then RmNum(1) else RmNum(0)), env)
  | (RmLessEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams  env e2) in (RmLessEqualTo(RmNum(n),e2'),env')
  | (RmLessEqualTo(RmStream(tT,n), RmStream(_,m))) -> 
      let rec recurse x y = match (x,y) with 
        | (Stream(a,ae),Stream(b,be)) -> 
           Stream(
            (let (e,_) = (eval1M inStreams env (RmLessEqualTo(a,b))) in e),
            function () -> recurse (ae()) (be())
          )
        | (StreamEnd(),StreamEnd()) -> Stream(RmNum(1), function() -> StreamEnd())
        | (StreamEnd(),_)
        | (_,StreamEnd()) -> StreamEnd()
      in (RmStream(tT, recurse n m), env)
  | (RmLessEqualTo(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmLessEqualTo(RmStream(tT, s),e2'), env')
  | (RmLessEqualTo(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmLessEqualTo(e1',e2),env')

  (* Greater Than *)
  | (RmGreaterThan(RmNum(n),RmNum(m))) -> ((if n>m then RmNum(1) else RmNum(0)), env)
  | (RmGreaterThan(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmGreaterThan(RmNum(n),e2'),env')
  | (RmGreaterThan(RmStream(tT,n), RmStream(_,m))) -> 
      let rec recurse x y = match (x,y) with 
        | (Stream(a,ae),Stream(b,be)) -> 
           Stream(
            (let (e,_) = (eval1M inStreams env (RmGreaterThan(a,b))) in e),
            function () -> recurse (ae()) (be())
          )
        | (StreamEnd(),_)
        | (_,StreamEnd()) -> StreamEnd()
      in (RmStream(tT, recurse n m), env)
  | (RmGreaterThan(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmGreaterThan(RmStream(tT, s),e2'), env')
  | (RmGreaterThan(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmGreaterThan(e1',e2),env')

  (* Greater Equal *)
  | (RmGreaterEqualTo(RmUnit(),RmUnit())) -> (RmNum(1),env)
  | (RmGreaterEqualTo(RmUnit(),e2))        ->
      (match e2 with 
          RmStream(tT,StreamEnd()) -> (RmNum(1),env)
        | RmStream(_,_) -> (RmNum(0),env)
        | _ -> let (e2',env') = (eval1M inStreams env e2)
               in (RmGreaterEqualTo(e2',RmUnit()), env)
      )
  | (RmGreaterEqualTo(e1,RmUnit()))        ->
      (match e1 with 
          RmStream(tT,StreamEnd()) -> (RmNum(1),env)
        | RmStream(_,_) -> (RmNum(0),env)
        | _ -> let (e1',env') = (eval1M inStreams env e1)
               in (RmGreaterEqualTo(e1',RmUnit()), env)
      )
  | (RmGreaterEqualTo(RmNum(n),RmNum(m))) -> ((if n>m then RmNum(1) else RmNum(0)), env)
  | (RmGreaterEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmGreaterEqualTo(RmNum(n),e2'),env')
  | (RmGreaterEqualTo(RmStream(tT,n), RmStream(_,m))) -> 
    let rec recurse x y = match (x,y) with 
      | (Stream(a,ae),Stream(b,be)) -> 
         Stream(
          (let (e,_) = (eval1M inStreams env (RmGreaterEqualTo(a,b))) in e),
          function () -> recurse (ae()) (be())
        )
      | (StreamEnd(),StreamEnd()) -> Stream(RmNum(1), function() -> StreamEnd())
      | (StreamEnd(),_)
      | (_,StreamEnd()) -> StreamEnd()
    in (RmStream(tT, recurse n m), env)
  | (RmGreaterEqualTo(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmGreaterEqualTo(RmStream(tT, s),e2'), env')
  | (RmGreaterEqualTo(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmGreaterEqualTo(e1',e2),env')

  (* Equal To *)
  | (RmEqualTo(RmUnit(),RmUnit())) -> (RmNum(1),env)
  | (RmEqualTo(RmUnit(),e2))        ->
      (match e2 with 
          RmStream(tT,StreamEnd()) -> (RmNum(1),env)
        | RmStream(_,_) -> (RmNum(0),env)
        | _ -> let (e2',env') = (eval1M inStreams env e2)
               in (RmEqualTo(e2',RmUnit()), env)
      )
  | (RmEqualTo(e1,RmUnit()))        ->
      (match e1 with 
          RmStream(tT,StreamEnd()) -> (RmNum(1),env)
        | RmStream(_,_) -> (RmNum(0),env)
        | _ -> let (e1',env') = (eval1M inStreams env e1)
               in (RmEqualTo(e1',RmUnit()), env)
      )
  | (RmEqualTo(RmNum(n),RmNum(m))) -> ((if n=m then RmNum(1) else RmNum(0)), env)
  | (RmEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmEqualTo(RmNum(n),e2'),env')
  | (RmEqualTo(RmStream(tT,n), RmStream(_,m))) -> 
    let rec recurse x y = match (x,y) with 
      | (Stream(a,ae),Stream(b,be)) -> 
         Stream(
          (let (e,_) = (eval1M inStreams env (RmEqualTo(a,b))) in e),
          function () -> recurse (ae()) (be())
        )
      | (StreamEnd(),StreamEnd()) -> Stream(RmNum(1), function() -> StreamEnd())
      | (StreamEnd(),_)
      | (_,StreamEnd()) -> StreamEnd()
    in (RmStream(tT, recurse n m), env)
  | (RmEqualTo(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmEqualTo(RmStream(tT, s),e2'), env')
  | (RmEqualTo(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmEqualTo(e1',e2),env')

  (* Not Equal *)
  | (RmNotEqualTo(RmUnit(),RmUnit())) -> (RmNum(0),env)
  | (RmNotEqualTo(RmUnit(), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmNotEqualTo(RmUnit(),e2'),env')
  | (RmNotEqualTo(_,RmUnit()))        -> (RmNum(1), env)
  | (RmNotEqualTo(RmNum(n),RmNum(m))) -> ((if n<>m then RmNum(1) else RmNum(0)), env)
  | (RmNotEqualTo(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmNotEqualTo(RmNum(n),e2'),env')
  | (RmNotEqualTo(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M inStreams env (RmNotEqualTo(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmNotEqualTo(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmNotEqualTo(RmStream(tT, s),e2'), env')
  | (RmNotEqualTo(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmNotEqualTo(e1',e2),env')

  (* Constructors *)
    | (RmCons(RmStream(nT,s), m)) ->
      (RmStream(
        (RivStream(nT)),
        Stream(
          RmStream(
            nT,
            s
          ),
          (function() -> Stream(
                (evalloop inStreams env m),
                function() -> StreamEnd()))
        )
      ), env)
  | (RmCons(e1,e2)) -> let(e1',env') = (eval1M inStreams env e1) in (RmCons(e1', e2), env')

  (* Append *)
  | (RmAppend(RmStream(nT,n), m)) ->
      (* Debug Code *)
      (* print_string "Appending two streams:\n";
      print_res_old (RmStream(nT,n));
      print_string  "\n"; *)
      (* / Debug Code *)
      let rec recurse x y = (
        match (x,y) with
        | (Stream(a,ae), b) -> 
           Stream(a, function() -> (recurse (ae()) b))
        | (StreamEnd(),b) -> 
        (
          match (evalloop inStreams env b) with 
          | RmStream(tT,o) -> o
          | _ -> raise (RuntimeError "Appending to non stream") 
        )
        )
      in ((RmStream(nT,(recurse n m))), env)
  | (RmAppend(e1,e2))                          -> let(e1',env') = (eval1M inStreams env e1) in (RmAppend(e1', e2), env')

  (* Operators *)
  | (RmPlus(RmNum(n),RmNum(m))) -> (RmNum(n+m) , env)
  | (RmPlus(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmPlus(RmNum(n),e2'), env')
  | (RmPlus(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M inStreams env (RmPlus(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmPlus(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmPlus(RmStream(tT, s),e2'), env')
  | (RmPlus(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmPlus(e1', e2), env')

  (* Minus *)
  | (RmMinus(RmNum(n),RmNum(m))) -> (RmNum(n-m) , env)
  | (RmMinus(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmMinus(RmNum(n),e2'), env')
  | (RmMinus(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M inStreams env(RmMinus(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmMinus(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmMinus(RmStream(tT, s),e2'), env')
  | (RmMinus(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmMinus(e1', e2), env')

  (* Multiply *)
  | (RmMultiply(RmNum(n),RmNum(m))) -> (RmNum(n*m) , env)
  | (RmMultiply(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmMultiply(RmNum(n),e2'), env')
  | (RmMultiply(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M inStreams env(RmMultiply(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmMultiply(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmMultiply(RmStream(tT, s),e2'), env')  
  | (RmMultiply(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmMultiply(e1', e2), env')

  (* Divide *)
  | (RmDivide(RmNum(n),RmNum(m))) -> (RmNum(n/m) , env)
  | (RmDivide(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmDivide(RmNum(n),e2'), env')
  | (RmDivide(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M inStreams env(RmDivide(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmDivide(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmDivide(RmStream(tT, s),e2'), env')  
  | (RmDivide(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmDivide(e1', e2), env')

  (* Modulus *)
  | (RmModulus(RmNum(n),RmNum(m))) -> (RmNum(n mod m) , env)
  | (RmModulus(RmNum(n), e2))      -> let (e2',env') = (eval1M inStreams env e2) in (RmModulus(RmNum(n),e2'), env')
  | (RmModulus(RmStream(tT,n), RmStream(_,m))) -> 
  let rec recurse x y = match (x,y) with 
    | (Stream(a,ae),Stream(b,be)) -> 
       Stream(
        (let (e,_) = (eval1M inStreams env(RmModulus(a,b))) in e),
        function () -> recurse (ae()) (be())
      )
    | (StreamEnd(),_)
    | (_,StreamEnd()) -> StreamEnd()
  in (RmStream(tT, recurse n m), env)
  | (RmModulus(RmStream(tT, s), e2)) -> let (e2',env') = (eval1M inStreams env e2) in (RmModulus(RmStream(tT, s),e2'), env')  
  | (RmModulus(e1, e2))            -> let (e1',env') = (eval1M inStreams env e1) in (RmModulus(e1', e2), env')

  (* Unary Minus *)
  | (RmUMinus(RmNum(n))) -> (RmNum(-n), env)
  | (RmUMinus(RmStream(tT,n))) -> 
  let rec recurse x = match x with 
    | Stream(a,ae)-> 
       Stream(
        (let (e,_) = (eval1M inStreams env(RmUMinus(a))) in e),
        function () -> recurse (ae())
      )
    | StreamEnd() -> StreamEnd()
  in (RmStream(tT, recurse n), env)
  | (RmUMinus(e1))      -> let (e1',env') = (eval1M inStreams env e1) in (RmUMinus(e1'), env')

  (* Ternary *)
  | (RmIf(RmStream(_,StreamEnd()),e1,e2))       
  | (RmIf(RmNum(0),e1,e2))        -> (e2, env)
  | (RmIf(RmNum(_),e1,e2))        -> (e1, env)
  | (RmIf(RmStream(tT,Stream(n,_)),e1,e2)) -> (RmIf(n,e1,e2), env)
  | (RmIf(b,e1,e2))               -> let (b',env') = (eval1M inStreams env b) in (RmIf(b',e1,e2), env')

  (* Let *)
  | (RmLet(tT,x,e1,e2)) when (isValue(e1)) -> (e2, addBinding env x e1)
  | (RmLet(tT,x,e1,e2))                    -> let (e1', env') = (eval1M inStreams (addBinding env x e1) e1) in (RmLet(tT,x,e1',e2), env')

  (* Application *)
  | (RmApp(RmLbd(rT,tT,x,e), e2)) when (isValue(e2)) -> (e, addBinding env x e2)
  | (RmApp(RmLbd(rT,tT,x,e), e2))                    -> let (e2',env') = (eval1M inStreams env e2) in (RmApp( RmLbd(rT,tT,x,e) , e2'), env')

  | (RmApp(RmLbdEmpty(rT,e), e2)) when (isValue(e2)) -> (e, env)
  | (RmApp(RmLbdEmpty(rT,e), e2))                    -> let (e2',env') = (eval1M inStreams env e2) in (RmApp(RmLbdEmpty(rT,e),e2'), env')

  | (RmApp(e1,e2))                                -> let (e1',env') = (eval1M inStreams env e1) in (RmApp(e1',e2), env') 

  (* Indexing *)
  | (RmIndex(RmStream(tT,s), RmStream(_,Stream(RmNum(n),_)))) -> 
    ((match (followNSteps s n) with 
      | Stream(RmNum(x),n) -> RmStream(RivInt,Stream(RmNum(x), function() -> StreamEnd()))
      | Stream(x,n) -> x
      | StreamEnd() -> RmUnit()),
       env
     )
  | (RmIndex(RmStream(tT,s), e)) -> let (e',env') = (eval1M inStreams env e) in ((RmIndex(RmStream(tT,s),e')), env')
  | (RmIndex(e, v)) -> let (e',env') = (eval1M inStreams env e) in ((RmIndex(e',v)), env')

  (* Section End *)
  | (RmSectionEnd(RmStream(tT,s), RmStream(_,Stream(RmNum(n),_)))) -> 
    (
      RmStream(tT,(followNSteps s n)),
       env
     )
  | (RmSectionEnd(RmStream(tT,s), e)) -> let (e',env') = (eval1M inStreams env e) in ((RmSectionEnd(RmStream(tT,s),e')), env')
  | (RmSectionEnd(e, v)) -> let (e',env') = (eval1M inStreams env e) in ((RmSectionEnd(e',v)), env')

  (* Section Start *)
  | (RmSectionStart(RmStream(tT,s), RmStream(_,Stream(RmNum(n),_)))) -> 
    (
      RmStream(tT,(endAtN s n)),
       env
     )
  | (RmSectionStart(RmStream(tT,s), e)) -> let (e',env') = (eval1M inStreams env e) in ((RmSectionStart(RmStream(tT,s),e')), env')
  | (RmSectionStart(e, v)) -> let (e',env') = (eval1M inStreams env e) in ((RmSectionStart(e',v)), env')

  (* Sections *)
  | (RmSection(RmStream(tT,s), RmStream(_,Stream(RmNum(nFrom),_)), RmStream(_,Stream(RmNum(nTo),_)))) ->
    let length = (nTo - nFrom) in
    if  length < 0 then
      raise (RuntimeError "Splitting 'from' value is greater than 'to' value")
    else
      (
        RmStream(tT,(endAtN (followNSteps s nFrom) length)),
         env
      )
  | (RmSection(RmStream(tT,s), RmStream(tT2,Stream(RmNum(nFrom),n1)), e)) -> let (e',env') = (eval1M inStreams env e) in (
    (RmSection(RmStream(tT,s), RmStream(tT2,Stream(RmNum(nFrom),n1)), e')), env')
  | (RmSection(RmStream(tT,s), e, n2)) -> let (e',env') = (eval1M inStreams env e) in ((RmSection(RmStream(tT,s), e', n2)), env')
  | (RmSection(e, n1, n2)) -> let (e',env') = (eval1M inStreams env e) in ((RmSection(e',n1, n2)), env')

  | (RmRead()) -> (inStreams , env)
  | _ -> raise (Terminated "Parsing encountered an unknown type")

and evalloop inStreams env e = try ( let (e',env') = (eval1M inStreams env e) in (evalloop inStreams env' e')) with Terminated _ -> if (isValue e) then e else raise (StuckTerm "Eval loop stuck on term") ;;

let evalProg inputBuffer e = evalloop (RmStream(RivStream(RivInt), (transpose (convertToStream (List.rev inputBuffer))))) (Env[]) e ;;

let rec append_streams x y = match (x,y) with
  | (Stream(a,ae), b) -> 
           Stream(a, function() -> (append_streams (ae()) b))
  | (StreamEnd(),b) -> b
  | (_,StreamEnd()) -> StreamEnd()

let rec count_streams streams acc = match streams with
  | Stream(n,e) -> count_streams (e()) (acc + 1)
  | StreamEnd() -> acc

let rec rearrange_stream stream nextValue nextValueType =
  match stream with 
    | Stream(RmStream(tT2,Stream(RmNum(n),ne)), nextStream) ->
            let nextElement = (Stream(RmStream(nextValueType, nextValue), function () -> StreamEnd())) in
            let newStream = (append_streams stream nextElement) in
              newStream
    | StreamEnd() -> (Stream(RmStream(RivStream(nextValueType),(nextValue)), function () -> StreamEnd()))
    | _ -> raise (DimensionError "Streams should be two dimensional")
;;


let rec print_streams_rec streams =
 match streams with 
  | Stream(RmStream(tT,n), e) ->
  (* Print a single line *)
    print_streams_rec n; 
    print_string "\n";
    print_streams_rec (e());
  (* Print a single line *)
  | Stream(RmNum(n), e) ->
    print_int n;
    print_string " ";
    print_streams_rec (e());
  | StreamEnd() -> ()
  | _ -> ()
;;

let rec print_streams streams = 
  match streams with 
  (* if the stream is 2D, print it transposed *)
  | Stream(RmStream(tT,_), _) ->
    (* print_res_old (RmStream(tT,streams)); *)
    print_streams_rec (transpose streams);
  (* Otherwise convert it to a 2D stream and transpose it *)
  | Stream(RmNum(_), _) ->
    print_streams_rec (transpose (Stream(RmStream(RivInt,streams), function () -> StreamEnd())));
  | StreamEnd() -> ()
  | _ -> raise (DimensionError "Input isn't being evaluated as a stream")


let rec print_res res = match res with
  | RmNum (i) -> print_int i
  | RmUnit () -> print_string "() "
  | RmStream (tT, s) -> print_streams(s)
  | RmLbd(rT,tT,x,e) -> print_string("Function : " ^ type_to_string( typeProg (res) ))
  | RmLbdEmpty(rT,e) -> print_string("Function : " ^ type_to_string( typeProg (res) ))
  | _ -> raise (NonBaseTypeResult "Not able to output result as string")
;;

