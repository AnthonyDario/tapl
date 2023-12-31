(* 
 * Typically these would all contain an "info"
 * type that stores where the node originated in
 * the source file (line number etc...) this would
 * be generated by the parser. I'm omitting it for
 * now 
 *)

(* The terms of our arithmetic language *)
type term =
    TmTrue
  | TmFalse
  | TmIf     of term * term * term
  | TmZero
  | TmSucc   of term
  | TmPred   of term
  | TmIsZero of term ;;

(* We will need to know if a term is numeric *)
let rec isnumericval t = match t with
    TmZero     -> true
  | TmSucc(t1) -> isnumericval t1
  | _          -> false ;;

(* We also need to know if a term is a value 
 * (i.e. a boolean or a number)
 *)
let rec isval t = match t with
    TmTrue                -> true
  | TmFalse               -> true
  | t when isnumericval t -> true
  | _                     -> false ;;

(* We will now implement the single-step evaluation
 * rules.  If we run into a term then the evaluation
 * function cannot produce a result, so we throw an
 * exception 
 *)
exception NoRuleApplies ;;

(* Single step evaluator *)
let rec eval1 t = match t with
    TmIf(TmTrue, b1, b2)  -> b1
  | TmIf(TmFalse, b1, b2) -> b2
  | TmIf(c, b1, b2)       -> TmIf(eval1 c, b1, b2)
  | TmSucc(t)             -> TmSucc(eval1 t)
  | TmPred(TmZero)        -> TmZero
  | TmPred(TmSucc(nv)) 
    when isnumericval nv  -> nv
  | TmPred(t)             -> TmPred(eval1 t)
  | TmIsZero(TmZero)      -> TmTrue
  | TmIsZero(TmSucc(nv)) 
    when isnumericval nv  -> TmFalse
  | TmIsZero(t)           -> TmIsZero(eval1 t)
  | _                     -> raise NoRuleApplies ;;

(* Now evaluate *)
let rec eval t =
    try let t' = eval1 t
        in eval t'
    with NoRuleApplies -> t ;;

(* Big step *)
let rec beval t = match t with
    _ when isval t -> t
  | TmIf(t1, t2, t3) 
    when beval t1 == TmTrue  -> beval t2
  | TmIf(t1, t2, t3)
    when beval t2 == TmFalse -> beval t3
  | TmSucc(t1) 
    when isnumericval (beval t1) -> beval t1
  | TmPred(t1)
    when beval t1 == TmZero -> TmZero
  | TmPred(t1)
    when match beval(t1) with
           TmSucc(nv1) 
           when isnumericval nv1 -> true
         | _                     -> false
            -> beval(t1)
  | TmIsZero(t1)
    when beval t1 == TmZero -> TmTrue
  | TmIsZero(t1)
    when match beval t1 with
           TmSucc(nv1) 
           when isnumericval nv1 -> true
         | _                     -> false
            -> TmFalse
  | _       -> raise NoRuleApplies ;;

(* Tests *)
(* -------------------- *)

(* Some helpers for outputting results *)
exception CannotPrint ;;
exception NotANumber  ;;

let rec toNum t = match t with
    TmZero     -> 0
  | TmPred(t1) -> (toNum t1) - 1
  | TmSucc(t1) -> (toNum t1) + 1
  | _          -> raise NotANumber ;;

let rec toString t = match t with
    TmTrue    -> "true" 
  | TmFalse   -> "false" 
  | TmZero 
  | TmPred(_) 
  | TmSucc(_) -> string_of_int (toNum t)
  | _         -> raise CannotPrint ;;

let rec print t = Printf.printf "%s\n" (toString t) ;;

(* The actual tests -- These should all output true *)
(* If true then true else false *)
print (eval 
    (TmIf (TmTrue, TmTrue, TmFalse)));;

print (beval
    (TmIf (TmTrue, TmTrue, TmFalse)));;

(* If false then false else true *)
print (eval 
    (TmIf (TmFalse, TmFalse, TmTrue)));;

print (beval 
    (TmIf (TmFalse, TmFalse, TmTrue)));;

(* If (isZero 3) then false else true *)
print (eval
    (TmIf (TmIsZero (TmSucc (TmSucc (TmSucc (TmZero)))),
        TmFalse, TmTrue))) ;;

print (beval
    (TmIf (TmIsZero (TmSucc (TmSucc (TmSucc (TmZero)))),
        TmFalse, TmTrue))) ;;

(* If (isZero 0) then true else false *)
print (eval
    (TmIf ((TmIsZero TmZero), TmTrue, TmFalse))) ;;

print (beval
    (TmIf (TmIsZero (TmSucc (TmSucc (TmSucc (TmZero)))),
        TmFalse, TmTrue))) ;;

(* 4 *)
print (TmSucc (TmSucc (TmSucc (TmSucc TmZero)))) ;;
