(* file: many_sorted.sml *)
(* description: ManySorted *)
(* author: Hiroto Kato *)

signature MANY_SORTED =
sig
    eqtype sort_key
    type sort_spec = sort_key list * sort_key
    type ms_fun = Fun.key * sort_spec
    type ms_sign = ms_fun list
    type ms_term = Term.term * sort_key
    type sort_env = (Var.key * sort_key) list
    type ms_rule = Trs.rule * sort_key
    type ms_rules = ms_rule list
    type ms_eq = ms_rule
    type ms_eqs = ms_rules
    val sortOfMsTerm: ms_term -> sort_key
    val dropSortInMsTerm: ms_term -> Term.term
    val dropSortInMsTerms: ms_term list -> Term.term list
    val sortInference: ms_sign -> ms_term list -> sort_env option
    val sortInferenceStep: ms_sign -> ms_term list -> (Term.term * sort_key) list option
    val sortAssignInMsTerm: ms_sign -> ms_term -> sort_env
    val sortAssignInMsTerms: ms_sign -> ms_term list -> sort_env
    val isWellSortedMsTerm: ms_sign -> ms_term -> bool
    val toMsTerm: ms_sign -> Term.term -> ms_term
                                              
    val sortOfMsRule: ms_rule -> sort_key
    val dropSortInMsRule: ms_rule -> Comp.rule
    val dropSortInMsRules: ms_rules -> Comp.rules
    val sortAssignInMsRule: ms_sign -> ms_rule -> sort_env
    val sortAssignInMsRules: ms_sign -> ms_rules -> sort_env
    val isWellSortedMsRule: ms_sign -> ms_rule -> bool
    val isWellSortedMsRules: ms_sign -> ms_rules -> bool

    val sortOfMsEq: ms_eq -> sort_key
    val dropSortInMsEq: ms_eq -> Comp.rule
    val dropSortInMsEqs: ms_eqs -> Comp.eqs
    val sortAssignInMsEq: ms_sign -> ms_eq -> sort_env
    val sortAssignInMsEqs: ms_sign -> ms_eqs -> sort_env
    val isWellSortedMsEq: ms_sign -> ms_eq -> bool
    val isWellSortedMsEqs: ms_sign -> ms_eqs -> bool

    val rdSort: string -> sort_key
    val prSort: sort_key -> string
    val rdSortSpec: string -> sort_spec
    val prSortSpec: sort_spec -> string
    val rdMsFun: string -> ms_fun
    val prMsFun: ms_fun -> string
    val prMsFuns: ms_fun list -> string 
    val sortOfFun: ms_sign -> Fun.key -> sort_spec

    val memberMsRule: ms_rule -> ms_rules -> bool
    val diffMsRules: ms_rules * ms_rules -> ms_rules
end

structure ManySorted : MANY_SORTED =
struct
local
    structure AL = AssocList
    structure LU = ListUtil
    structure T = Term
    structure LP = ListPair
    structure L = List
in

type sort_key = string
type sort_spec = sort_key list * sort_key
type ms_fun = Fun.key * sort_spec
type ms_sign = ms_fun list
type ms_term = Term.term * sort_key
type sort_env = (Var.key * sort_key) list
type ms_rule = (Term.term * Term.term) * sort_key
type ms_rules = ms_rule list
type ms_eq = ms_rule
type ms_eqs = ms_rules
                  
exception NotWellSorted
              
(* 多ソート項 *)
fun sortOfMsTerm (t,ty) = ty
fun dropSortInMsTerm (t,ty) = t
fun dropSortInMsTerms nil = nil
  | dropSortInMsTerms ((t,ty)::xs) = t::(dropSortInMsTerms xs)

(* 型推論 *)
fun sortInference sign cnstr =
    let
        fun main [] env = SOME env
          | main ((t,ty)::rest) env =
            if T.isVar t then
                case AL.find (Var.fromString (T.toString t)) env of
                    NONE => main rest (valOf (AL.add ((Var.fromString (T.toString t)),ty) env))
                  | SOME ty1 => if ty1=ty then main rest env else NONE
            else
                case AL.find (Fun.fromString (Symbol.toString (T.root t))) sign of
                    NONE => NONE
                  | SOME (tylist,ty1) => if ty1=ty
                                         then main (LU.union ((LP.map (fn (t0,ty0) => (t0,ty0)) (T.args t,tylist)),rest)) env
                                         else NONE
    in
        main cnstr []
    end

(* 1ステップの型推論 *)
fun sortInferenceStep sign cnstr =
    let
        fun main [] env = SOME env
          | main ((t,ty)::rest) env =
            if T.isVar t
            then SOME [(t,ty)]
            else
                case AL.find (Fun.fromString (Symbol.toString (T.root t))) sign of
                    NONE => NONE
                  | SOME (tylist,ty1) => if ty1=ty
                                         then SOME (LU.union (LP.map (fn (t0,ty0) => (t0,ty0)) (T.args t,tylist),nil))
                                         else NONE
    in
        main cnstr []
    end
        
        
fun sortAssignInMsTerms sign cnstr =
    case sortInference sign cnstr of
        NONE => raise NotWellSorted
      | SOME env => env
fun sortAssignInMsTerm sign (term,ty) =
    sortAssignInMsTerms sign [(term,ty)]
fun isWellSortedMsTerm sign (term,ty) =
    isSome (sortInference sign [(term,ty)])
fun toMsTerm sign term = if T.isVar term
                         then raise NotWellSorted
                         else (case AL.find (Fun.fromString (Symbol.toString (T.root term))) sign of
                                   NONE => raise NotWellSorted
                                 | SOME (sortl,key) => (term,key))

(* 多ソート項書き換え *)
fun sortOfMsRule (rule,ty) = ty
fun dropSortInMsRule (rule,ty) = rule
fun dropSortInMsRules msrules = L.map (fn (rule,ty) => rule) msrules
fun sortAssignInMsRule sign ((l,r),ty) =
    case sortInference sign ([(l,ty),(r,ty)]) of
        NONE => raise NotWellSorted
      | SOME env => env
fun sortAssignInMsRules sign msrules =
    LU.union (L.concat (L.map (fn msrule => sortAssignInMsRule sign msrule) msrules),nil)
fun isWellSortedMsRule sign ((l,r),ty) =
    isSome (sortInference sign [(l,ty),(r,ty)])
fun isWellSortedMsRules sign msrules =
    L.all (fn msrule => isWellSortedMsRule sign msrule) msrules

(* 多ソート項の等式 *)
fun sortOfMsEq (eq,ty) = ty
fun dropSortInMsEq (eq,ty) = eq
fun dropSortInMsEqs mseqs = L.map (fn (eq,ty) => eq) mseqs
fun sortAssignInMsEq sign ((s,t),ty) =
    case sortInference sign ([(s,ty),(t,ty)]) of
        NONE => raise NotWellSorted
      | SOME env => env
fun sortAssignInMsEqs sign mseqs =
    LU.union (L.concat (L.map (fn mseq => sortAssignInMsEq sign mseq) mseqs),nil)
fun isWellSortedMsEq sign ((s,t),ty) = 
    isSome (sortInference sign [(s,ty),(t,ty)])
fun isWellSortedMsEqs sign mseqs =
    L.all (fn mseq => isWellSortedMsEq sign mseq) mseqs

          
fun prSort str = str
fun prSortSpec ([],s) = prSort s
  | prSortSpec (ws,s) =
    (LU.toStringComma prSort ws) ^ "->" ^ (prSort s)
fun prMsFun (f,spec) = (Fun.toString f) ^ ":" ^ (prSortSpec spec)

fun prMsFuns nil = "\t[ ]\n\n"
  | prMsFuns l =
    let
        fun msFuns (t::nil) = "\t  " ^ (prMsFun t)
          | msFuns (t::ts) = "\t  " ^ (prMsFun t) ^ "\n" ^ (msFuns ts)
        fun msFunsf (t::nil) = (prMsFun t)
          | msFunsf (t::ts) = (prMsFun t) ^ "\n" ^ (msFuns ts)
    in
        "\t  " ^ (msFunsf l) ^ "  \n\n"
    end
        
fun rdSort str = str

structure SortSpecialSymbols =
struct val special = [#",",#"-",#">",#":"] end
structure SortLex = Lexical (SortSpecialSymbols)
structure SortParsing = Parsing (SortLex)

local
    fun makePair1 s = ([],s)
    fun makeList (s,ws) = s::ws
    fun makeList1 s = s::nil

    open SortParsing
    infix 6 $--
    infix 5 --
    infix 3 >>
    infix 0 ||

    fun msfun toks =
        ( id --  ":" $-- sortspec) toks
    and sortspec toks =
        ( sortseq -- "-" $-- (">" $-- id) || id >> makePair1 ) toks
    and sortseq toks =
        ( id -- "," $-- sortseq >> makeList || id >> makeList1 ) toks
                                                                 
in

fun rdMsFun str = reader msfun str
fun rdSortSpec str = reader sortspec str
                            
end (* of local *)

fun sortOfFun sign f =
    case AL.find f sign of
        SOME spec =>  spec
      | NONE => raise Fail "Error: ManySorted.sortOfFun: function without sort specification"

fun memberMsRule x ys = L.exists (fn y => Trs.equal (dropSortInMsTerm x) (dropSortInMsTerm y)) ys
(* xsからysを取り除く *)
fun diffMsRules (xs,ys) = L.filter (fn x => not(memberMsRule x ys)) xs
                                   
end (* of local *)
end
