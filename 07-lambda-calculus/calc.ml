(* As before each of these would contain an info
   field that represents the position in the file
   for error reporting *)

(* The variables are represented by their de bruijn
   indexes (Chapter 6).  This means we represent
   variable by the index of their associated
   abstraction where 0 is the nearest abstraction *)
type term = 
    TmVar of int * int
  | TmAbs of string * term
  | TmApp of term * term 

(* Printing *)
(* ------------------ *)
exception NoVariableFound

type binding = NameBind 
type context = (string * binding) list
let pr s = Printf.printf "%s" s

let rec ctxlength ctx = match ctx with
  | []      -> 0
  | (c::cs) -> 1 + ctxlength cs

let rec index2name ctx i = match ctx, i with
  | []     , _ -> raise NoVariableFound
  | (c::cs), 0 -> let (x, _) = c in x
  | (c::cs), i -> index2name cs (i - 1) 

(* If the name is in the ctx come up with a new one *)
let rec isnamebound ctx x = match ctx, x with
  | ([],      x) -> false
  | ((c::cs), x) -> let (i, _) = c in 
                    if x = i then true else isnamebound cs x

let rec pickfreshname ctx x = 
    if isnamebound ctx x 
    then pickfreshname ctx (x^"'")
    else ((x, NameBind)::ctx, x)

let rec printtm ctx t = match t with
    TmAbs(x, t1) ->
        let (ctx', x') = pickfreshname ctx x in
        pr "(lambda "; pr x'; pr ". "; printtm ctx' t1; pr ")"
  | TmApp(t1, t2) ->
    pr "("; printtm ctx t1; pr " "; printtm ctx t2; pr ")"
  | TmVar(x, n) ->
      if ctxlength ctx = n then
        pr (index2name ctx x)
      else
        pr "[bad index]" ;;

(* Evaluation *)
(* ------------------- *)

(* In order to have a substitution for our variables 
   we need a shifting to renumber the free variables
   in a term.  When substituting our context becomes
   longer by one inside of the term.  We have to
   make sure that we only shift free variables, not
   bound ones. *)
let termShift d t =
  let rec walk c t = match t with
    TmVar(x, n)   -> if x >= c then TmVar(x + d, n + d)
                     else TmVar(x, n + d)
  | TmAbs(x, t1)  -> TmAbs(x, walk (c + 1) t1)
  | TmApp(t1, t2) -> TmApp(walk c t1, walk c t2)
  in walk 0 t ;;

(* Now we can write the substitution function, using
   shifting. *)
let termSubst j s t =
  let rec walk c t = match t with
    TmVar(x, n)   -> if x = j + c then termShift c s 
                     else TmVar(x, n)
  | TmAbs(x, t1)  -> TmAbs(x, walk (c + 1) t1)
  | TmApp(t1, t2) -> TmApp(walk c t1, walk c t2)
  in walk 0 t

(* For beta reduction multiple steps are performed
   First we shift the substituted term by one, then
   substitute, then shift the whole result down *)
let termSubstTop s t =
    termShift (-1) (termSubst 0 (termShift 1 s) t)

(* Helper to determine if a node is a value. *)
let rec isval ctx t = match t with
    TmAbs(_, _) -> true
  | _ -> false

(* And single-step evaluation is pretty straight
 * forward just transcribe the evaluation rules.
 *
 *        t1 -> t1'
 *    -----------------  (E-APP1)
 *     t1 t2 -> t1' t2
 *
 *
 *        t2 -> t2'
 *    -----------------  (E-APP2)
 *     v1 t2 -> v1 t2'
 *
 *
 *    (\x.t12) v2 -> [x -> v2]t12  (E-APPABS)
 *
 *  Note that these rulse mean we reduce the function
 *  until it is a lambda abstraction, then we reduce the
 *  parameter, then we perform any substitution.
 *)
exception NoRuleApplies

(* Single step *)
let rec eval1 ctx t = match t with
    TmApp(TmAbs(x, t12), v2) when isval ctx v2 ->
        termSubstTop v2 t12
  | TmApp(v1, t2) when isval ctx v1 ->
        let t2' = eval1 ctx t2 in
        TmApp(v1, t2')
  | TmApp(t1, t2) ->
        let t1' = eval1 ctx t1 in
        TmApp(t1', t2)
  | _ -> raise NoRuleApplies

let rec eval ctx t =
    try let t' = eval1 ctx t
        in eval ctx t'
    with NoRuleApplies -> t

(* Exercise 7.3.1 write the evaluation function for
 * big-step semantics 
 *  
 *   t1 => \x.t12, t2 => v2, [x -> v2]t12 => t'
 *  --------------------------------------------
 *                  t1 t2 => t'
 *)

let rec evaln ctx t = match t with
    TmApp(TmAbs(x, t12), t2) ->
        let v2 = evaln ctx t2 in
        let t' = evaln ctx (termSubstTop v2 t12) in
        t'
  | _ -> t

(* Testing *)
(* --------------------------- *)

(* \x.x *)
let t1 = (TmAbs ("x", TmVar(0, 1))) ;;
printtm [] t1;

pr "\n"

(* \f. (\x. f (x x)) (\x. f (x x)) *)
let p = TmAbs ("f", 
       TmApp (TmAbs ("x", 
                     TmApp (TmVar (1, 2), 
                            TmApp (TmVar (0, 2), 
                                   TmVar (0, 2)))),
             (TmAbs ("x", 
                     TmApp (TmVar (1, 2),
                            TmApp (TmVar (0, 2), 
                                   TmVar (0, 2))))))) ;;

printtm [] p ;;
pr "\n" ;;

(* (\x. x x) (\x. x) *)
let p =
    TmApp (TmAbs ("x",
                  TmApp (TmVar (0, 1),
                         TmVar (0, 1))),
           TmAbs ("x",
                  TmVar (0, 1))) ;;

printtm [] p ;;
pr "\n" ;;

printtm [] (eval [] p) ;;
pr "\n" ;;

printtm [] (evaln [] p) ;;
pr "\n" ;;

(* (\x. (\x.x) x) (\y.y y) *)
let p = 
    TmApp (TmAbs ("x",
                  TmApp (TmAbs ("x",
                                TmVar (0, 2)),
                         TmVar (0, 1))),
           TmAbs ("y",
                  TmApp (TmVar (0, 1),
                         TmVar (0, 1)))) ;;

printtm [] p ;;
pr "\n" ;;

printtm [] (eval [] p) ;;
pr "\n" ;;

printtm [] (evaln [] p) ;;
pr "\n" ;;

(* (\x. (\x.x) (\y.y x)) (\x.x) *)
let p =
    TmApp (TmAbs ("x",
                  TmApp (TmAbs ("x",
                                TmVar (0, 2)),
                         TmAbs ("y",
                                TmApp (TmVar (0, 2),
                                       TmVar (1, 2))))),
           TmAbs ("x", TmVar (0, 1))) ;;

printtm [] p ;;
pr "\n" ;;

printtm [] (eval [] p) ;;
pr "\n" ;;

printtm [] (evaln [] p) ;;
pr "\n" ;;
