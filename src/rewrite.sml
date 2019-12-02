(* file: rewrite.sml *)
(* description: rewriting and ordered rewriting *)
(* author: Hiroto Kato *)

signature REWRITE = 
sig
    (* rewriting*)
    val rootStep: Trs.trs -> Term.term -> Term.term option 
    val step: Trs.trs -> Term.term -> Term.position -> Term.term option
    val listep: Trs.trs -> Term.term -> Term.term option
    val isNF: Trs.trs -> Term.term -> bool 
    val listepsToNF: Trs.trs -> Term.term -> unit 
    val linf: Trs.trs -> Term.term -> Term.term
    val isJoinable: Trs.trs -> Term.term * Term.term -> bool
    (* ordered rewriting *)
    val rootStepOrder: (Trs.trs * (Trs.rule -> bool)) -> Term.term -> Term.term option 
    val stepOrder: (Trs.trs * (Trs.rule -> bool)) -> Term.term -> Term.position -> Term.term option
    val listepOrder: (Trs.trs * (Trs.rule -> bool)) -> Term.term -> Term.term option
    val isNFOrder: (Trs.trs * (Trs.rule -> bool)) -> Term.term -> bool
    val linfOrder: (Trs.trs * (Trs.rule -> bool)) -> Term.term -> Term.term
end

structure Rewrite: REWRITE =
struct 

local 
    structure L = List
    structure S = Subst
    structure T = Term
in

(* rootStep rs term : TRS rs による根位置での書き換え *)
fun rootStep [] term = NONE
  | rootStep ((l,r)::rs) term = 
    case S.match l term
     of SOME sigma => SOME (T.fillContext (T.makeContext term nil) (S.apply sigma r))
      | NONE => rootStep rs term

(* 項の指定した位置での書き換え *)
fun step [] term p = NONE
  | step rs term p = 
    case rootStep rs (T.subterm term p) 
     of SOME t => SOME (T.fillContext (T.makeContext term p) t)
      | NONE => NONE
                    
(* 最左最内書き換え *)
fun listep [] term = NONE
  | listep trs term =
    let 
        fun redexpos nil = nil
          | redexpos (p::ps) = 
            case step trs term p
             of SOME t => p::(redexpos ps)
              | NONE => (redexpos ps)
                            
        fun lipos x nil = x
          | lipos x (p::ps) = if (L.length x) > (L.length p)
                              then lipos x ps 
                              else lipos p ps
    in
        step trs term (lipos nil (L.rev(redexpos (T.pos term))))
    end

(* 正規形かどうかの判定 *)
fun isNF trs term = case listep trs term 
                     of NONE => true
                      | _ => false

(* 正規形になるまで最左最内書き換えを1ステップずつ表示 *)
fun listepsToNF [] term = print "\n"
  | listepsToNF trs term =
    let
        fun listepsToNFToString trs term =
            case isNF trs term
             of true => "->R "^(T.toString term)^"\n"
              | false => ("->R "^(T.toString term)^"\n")^(listepsToNFToString trs (valOf(listep trs term)))
    in
        print ("    "^(T.toString term)^"\n"^(listepsToNFToString trs term))
    end
        
(* 最左最内書き換えによって、与えられた項の正規形を求める *)
fun linf [] term = term
  | linf trs term =
    case isNF trs term
     of true => term
      | false => linf trs (valOf(listep trs term))

(* 2つの項の交差性を判定する関数 *)
fun isJoinable trs (t1,t2) = if t1=t2
                             then true
                             else (isJoinable trs (t1,valOf(listep trs t2))) orelse (isJoinable trs (valOf(listep trs t1),t2))


(* ordered rewriting *)
(* 根位置での書き換え(s->t and s>t) *)
fun rootStepOrder ([],grter) term = NONE
  | rootStepOrder ((l,r)::rs,grter) term = 
    case S.match l term
     of SOME sigma => if grter (term,T.fillContext (T.makeContext term nil) (S.apply sigma r))
                      then SOME (T.fillContext (T.makeContext term nil) (S.apply sigma r))
                      else rootStepOrder (rs,grter) term
      | NONE => rootStepOrder (rs,grter) term
                              
(* 項の指定した位置での書き換え(s->t and s>t) *)
fun stepOrder ([],grter) term p = NONE
  | stepOrder (rs,grter) term p = 
    case rootStepOrder (rs,grter) (T.subterm term p) 
     of SOME t => SOME (T.fillContext (T.makeContext term p) t)
      | NONE => NONE
                    
(* 最左最内書き換え(s->t and s>t) *)
fun listepOrder ([],grter) term = NONE
  | listepOrder (trs,grter) term = 
    let
        fun redexpos nil = nil
          | redexpos (p::ps) = 
            case stepOrder (trs,grter) term p
             of SOME t => p::(redexpos ps)
              | NONE => (redexpos ps)
                            
        fun lipos x nil = x
          | lipos x (p::ps) = if (L.length x) > (L.length p)
                              then lipos x ps 
                              else lipos p ps
    in
        stepOrder (trs,grter) term (lipos nil (L.rev(redexpos (T.pos term))))
    end
        
(* 正規形かどうかの判定(s->t and s>t) *)
fun isNFOrder (trs,grter) term = case listepOrder (trs,grter) term 
                                  of NONE => true
                                   | _ => false
                                              
(* s->t and s>tの最左最内書き換えによって、与えられた項の正規形を求める *)
fun linfOrder (nil,grter) term = term
  | linfOrder (trs,grter) term =
    case isNFOrder (trs,grter) term
     of true => term
      | false => linfOrder (trs,grter) (valOf(listepOrder (trs,grter) term))

end (* of local *)

end
