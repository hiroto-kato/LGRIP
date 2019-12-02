(* file: trs.sml *)
(* description: first-order term rewriting systems *)
(* author: Hiroto Kato *)

signature TRS = 
sig 
    type trs = (Term.term * Term.term) list
    type rule = Term.term * Term.term
    type rules = (Term.term * Term.term) list
    val isTrs: rule -> bool
    val prRule: rule -> string
    val rdRule: string -> rule
    val prEq: rule -> string
    val rdEq: string -> rule
    val prEqs: rules -> string
    val prRules: rules -> string
    val rename: rule * rule -> rule * rule
    val renameRules: Term.var_key list -> rule -> rule
    val equal: rule -> rule -> bool
    val equalTerm: Term.term -> Term.term -> bool
                                                 
end

structure Trs: TRS =
struct

local 
    structure SU = StringUtil
    structure L = List
    structure LU = ListUtil
    structure T = Term       
in

type trs = (Term.term * Term.term) list
type rule = Term.term * Term.term
type rules = (Term.term * Term.term) list

fun isTrs (l,r) = 
    let
        val lvar = T.vars l
        val rvar = T.vars r
    in
        if not(T.isVar l) andalso L.all (fn v => LU.member v lvar) rvar
        then true
        else false   
    end
        
fun prRule (l,r) = (Term.toString l) ^ " -> " ^ (Term.toString r)
fun rdRule str = Term.readKeySeparatedTermPair "->" str 

fun prEq (l,r) = (Term.toString l) ^ " = " ^ (Term.toString r)
fun rdEq str = Term.readKeySeparatedTermPair "=" str 

fun prEqs nil = "\t[  ]\n"
  | prEqs l =
    let
        fun eqs (t::nil) = "\t  " ^ (prEq t)
          | eqs (t::ts) = "\t  " ^ (prEq t) ^ "\n" ^ (eqs ts)
        fun eqsf (t::nil) = (prEq t)
           |eqsf (t::ts) = (prEq t) ^ "\n" ^ (eqs ts)

    in
        "\t[ " ^ (eqsf l) ^ " ]\n"
    end

fun prRules nil = "\t[  ]\n\n"
  | prRules l = 
    let 
        fun rules (t::nil) = "\t  " ^ (prRule t)
          | rules (t::ts) = "\t  " ^ (prRule t) ^ "\n" ^ (rules ts)
        fun rulesf (t::nil) = (prRule t)
          | rulesf (t::ts) = (prRule t) ^ "\n" ^ (rules ts)
    in
        "\t[ " ^ (rulesf l) ^ " ]\n\n"
    end

(* 変数の名前替えをする関数 *)
fun rename ((l1,r1),(l2,r2)) = 
    let val vl = LU.union ((T.vars l1),(T.vars r1))
        val max = L.foldr (fn ((x,i),n) => Int.max (i,n)) 0 vl
        fun rename1 (T.Var (x,i)) = T.Var (x,max+i+1)
          | rename1 (T.Fun (f,ts)) = T.Fun (f, (L.map rename1 ts))
    in
        ((l1,r1),((rename1 l2),(rename1 r2)))
    end

fun renamex ((l1,r1),(l2,r2)) = 
    let val vl = LU.union ((T.vars l1),(T.vars r1))
        val max = L.foldr (fn ((x,i),n) => Int.max (i,n)) 0 vl
        fun rename1 (T.Var (x,i)) = T.Var (x,max+i+1)
          | rename1 (T.Fun (f,ts)) = T.Fun (f, (L.map rename1 ts))
    in
        ((l1,r1),((rename1 l2),(rename1 r2)))
    end
        
(* trsの変数の名前替えをする関数 *)
fun renameRules vars (l,r) =
    let
        val max  = L.foldr (fn ((x,i),n) => Int.max (i,n)) 0 vars
        fun rename1 (T.Var (x,i)) = T.Var (x,max+1)
          | rename1 (T.Fun (f,ts)) = T.Fun (f, (L.map rename1 ts))
    in
        ((rename1 l), (rename1 r))
    end

fun equal rule1 rule2 =
    let val ((l1,r1),(l2,r2)) = rename (rule1,rule2)
        exception Neq
        val sigma = case (Subst.matchVar l1 l2) of
                        NONE => raise Neq
                      | SOME sigma0 =>
                        L.concat (L.map (fn (x,T.Var(v,i)) =>
                                            [((v,i),T.Fun ("c"^T.toString (T.Var(v,i)), nil)),(x,T.Fun("c"^T.toString (T.Var(v,i)),nil))]) sigma0)
        val _ = case (Subst.matchVar (Subst.apply sigma r1) (Subst.apply sigma r2)) of
                    NONE => raise Neq
                  | SOME sigma => ()
    in
        true
    end
    handle Neq => false

(* 項と項が変数違いで等しい *)        
fun equalTerm t1 t2 =
    let
        exception Neq
        val _ = case Subst.matchVar t1 t2 of
                    NONE => raise Neq
                  | SOME sigma => ()
    in
        true
    end handle Neq => false

end (* of local *)

end
