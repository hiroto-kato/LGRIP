(* file: path_order.sml *)
(* description: path orders for termination check *)
(* author: Hiroto Kato  *)

signature PATH_ORDER = 
sig
    type prec = Fun.key * Fun.key -> bool
    val rdPrec: (Fun.key * int) list -> prec
    val lpoGt: prec -> (Term.term * Term.term) -> bool
    val isLpoDecreasingTrs: prec -> Trs.trs -> bool
    val encodeLpoGt: (Term.fun_key * Term.fun_key -> Formula.prop) -> (Term.term * Term.term) -> Formula.prop
    val checkLpoTermination: Trs.trs -> bool
    val qrdPrec: (Fun.key * int) list -> prec
    val lpqoGt: prec -> (Term.term * Term.term) -> bool
    val isLpqoDecreasingTrs: prec -> Trs.trs -> bool
    val encodeLpqoGt: (Term.fun_key * Term.fun_key -> Formula.prop) -> (Term.term * Term.term) -> Formula.prop
    val checkLpqoTermination: Trs.trs -> bool
                                             
end

structure PathOrder: PATH_ORDER =
struct
local
    structure AL = AssocList
    structure L = List
    structure T = Term
    structure F = Formula
    structure LU = ListUtil
in

type prec = Fun.key * Fun.key -> bool

fun rdPrec wlist (f,g) = case (AL.find f wlist ,AL.find g wlist) 
                          of (SOME v, SOME w) => v>w 
                           | (SOME v, NONE) => v>0
                           | (NONE,SOME w) => w>0
                           | (NONE,NONE) => false
                                                

(* 辞書式拡張 *)
fun lex rel ([],[]) = false
  | lex rel (x::xs,y::ys) = if rel (x, y) then true 
                            else (if x = y then lex rel (xs, ys)
                                  else false)
  | lex rel _ = raise Fail "Error: lex compares lists having different length"

(* 辞書式経路順序による比較 *)
fun lpoGt prec (term1,term2) = 
    let fun gt (T.Var _, _) = false
          | gt (T.Fun (f,ss), t as (T.Var _)) = geqforsome ss t
          | gt (s as (T.Fun (f,ss)), t as (T.Fun (g,ts))) = if f=g
                                                            then (geqforsome ss t) orelse ((lex gt (ss,ts)) andalso (gtforall s ts))
                                                            else (geqforsome ss t) orelse ((prec (f,g)) andalso (gtforall s ts))
                                                                                              
        and geq (s,t) = if s=t then true
                        else (gt (s,t))
        and gtforall s ts = L.all (fn ti => gt (s,ti)) ts
        and geqforsome ss t = L.exists (fn si => geq (si,t)) ss
    in gt (term1,term2)
    end

(* 辞書式経路順序による減少性判定 *)
fun isLpoDecreasingTrs prec rs = L.all (lpoGt prec) rs
                                       
(* Formula.procにエンコードする *)
fun encodeLpoGt prec (term1,term2) =
    let
        (* 辞書式拡張(エンコード) *)
        fun lexproc rel ([],[]) = F.False
          | lexproc rel (x::xs,y::ys) = F.IfThenElse (rel (x, y), F.True, (if x = y
                                                                           then lexproc rel (xs, ys)
                                                                           else F.False))
          | lexproc rel _ = raise Fail "Error: lex compares lists having different length"
                                  
        fun gt (T.Var _, _) = F.False
          | gt (T.Fun (f,ss), t as (T.Var _)) = geqforsome ss t
          | gt (s as (T.Fun (f,ss)), t as (T.Fun (g,ts))) = if f=g
                                                            then F.Or (geqforsome ss t , F.And (lexproc gt (ss,ts), gtforall s ts))
                                                            else F.Or (geqforsome ss t, F.And (prec (f,g), gtforall s ts))
                                                                      
        and geq (s,t) = if s=t then F.True
                        else (gt (s,t))
        and gtforall s ts = F.Conj (L.map (fn ti => gt (s,ti)) ts)
        and geqforsome ss t = F.Disj (L.map (fn si => geq (si,t)) ss)
    in
        gt (term1,term2)
    end

(* 辞書式経路順序に基づく停止性判定手続き *)
fun checkLpoTermination rs =
    let
        open Formula
        (* 関数記号と重み変数のテーブル *)
        val funs = List.foldr (fn ((l,r),fs) => LU.union (T.funs l, LU.union (Term.funs r, fs))) [] rs
        val vars = L.tabulate (L.length funs, fn x => Var x)
        val table = ListPair.zip (funs, vars)
        fun lookup f = valOf (AL.find f table)
        fun prec (f,g) = Atom (Gt (lookup f, lookup g))

        (* LPO termingation のエンコーディング *)
        val propGe0 = Conj (L.map (fn (_,x) => Atom (Ge (x, Const 0))) table)
        val propDist = Atom (Distinct (L.map (fn (_,x) => x) table))
        val propLpo = Conj (L.map (fn (s,t) => encodeLpoGt prec (s,t)) rs)
        val prop = Conj [propGe0,propDist,propLpo]

        (* assert formulas *)
        fun lpoTerminationInquiry outs =
            let
                val _ = L.app (fn x => TextIO.output (outs, Yices2.defineIntVar x)) (L.tabulate (L.length funs, fn x => x))
                val _ = TextIO.output (outs, Yices2.assertProp prop)
                val _ = TextIO.output (outs, "(check)\n")
                val _ = TextIO.output (outs, "(show-model)\n")
            in
                ()
            end
    in
        case Yices2.runSolver lpoTerminationInquiry of
            SOME assig =>
            let
                val _ = print "\n"
                val _ = L.app (fn (f,x) => print (f ^ ":" ^ (Int.toString (valOf (AL.find (Yices2.prArith x) assig))) ^ "\n")) table
            in true
            end
          | NONE => false
    end

fun qrdPrec wlist (f,g) = case (AL.find f wlist ,AL.find g wlist) 
                           of (SOME v, SOME w) => v>w orelse v=w
                            | (SOME v, NONE) => v>0
                            | (NONE,SOME w) => w>0
                            | (NONE,NONE) => false

(* 辞書式拡張 *)
fun qlex rel ([],[]) = false
  | qlex rel (x::nil,y::nil) = if rel (x,y) then true
                               else (if x = y then true
                                     else false)
  | qlex rel (x::xs,y::ys) = if rel (x,y) then true 
                             else (if x = y then qlex rel (xs,ys)
                                   else false)
                                      
fun lpqoGt prec (term1,term2) = 
    let fun gt (T.Var _, _) = false
          | gt (T.Fun (f,ss), t as (T.Var _)) = geqforsome ss t
          | gt (s as (T.Fun (f,ss)), t as (T.Fun (g,ts))) =
            if f=g
            then (geqforsome ss t) orelse ((qlex geq (ss,ts)) andalso (geqforall s ts))
            else (geqforsome ss t) orelse ((prec (f,g)) andalso (geqforall s ts))
        and geq (s,t) = if s=t
                        then true
                        else gt (s,t)
        and geqforall s ts = L.all (fn ti => geq (s,ti)) ts
        and geqforsome ss t = L.exists (fn si => geq (si,t)) ss
    in
        geq (term1,term2)
    end
        
fun isLpqoDecreasingTrs prec rs = L.all (lpqoGt prec) rs

fun encodeLpqoGt prec (term1,term2) =
    let
        (* 辞書式拡張(エンコード) *)
        fun qlexproc rel ([],[]) = F.False
          | qlexproc rel (x::nil,y::nil) = F.IfThenElse (rel (x,y), F.True, (if x=y
                                                                             then F.True
                                                                             else F.False))
          | qlexproc rel (x::xs,y::ys) = F.IfThenElse (rel (x,y), F.True, (if x=y
                                                                           then qlexproc rel (xs,ys)
                                                                           else F.False))
          | qlexproc rel _ = raise Fail "Error: lex compares lists having different length"
        fun gt (T.Var _, _) = F.False
          | gt (T.Fun (f,ss), t as (T.Var _)) = geqforsome ss t
          | gt (s as (T.Fun (f,ss)), t as (T.Fun (g,ts))) =
            if f=g
            then F.Or (geqforsome ss t , F.And (qlexproc geq (ss,ts), geqforall s ts))
            else F.Or (geqforsome ss t, F.And (prec (f,g), geqforall s ts))
        and geq (s,t) = if s=t
                        then F.True
                        else gt (s,t)
        and geqforall s ts = F.Conj (L.map (fn ti => geq (s,ti)) ts)
        and geqforsome ss t = F.Disj (L.map (fn si => geq (si,t)) ss)
    in
        geq (term1,term2)
    end
        
fun checkLpqoTermination rs =
    let
        open Formula
        (* 関数記号と重み変数のテーブル *)
        val funs = List.foldr (fn ((l,r),fs) => LU.union (T.funs l, LU.union (Term.funs r, fs))) [] rs
        val vars = L.tabulate (L.length funs, fn x => Var x)
        val table = ListPair.zip (funs, vars)
        fun lookup f = valOf (AL.find f table)
        fun prec (f,g) = Atom (Ge (lookup f, lookup g))

        (* LPO termingation のエンコーディング *)
        val propGe0 = Conj (L.map (fn (_,x) => Atom (Ge (x, Const 0))) table)
        val propDist = Atom (Distinct (L.map (fn (_,x) => x) table))
        val propLpo = Conj (L.map (fn (s,t) => encodeLpoGt prec (s,t)) rs)
        val prop = Conj [propGe0,propDist,propLpo]

        (* assert formulas *)
        fun lpqoTerminationInquiry outs =
            let
                val _ = L.app (fn x => TextIO.output (outs, Yices2.defineIntVar x)) (L.tabulate (L.length funs, fn x => x))
                val _ = TextIO.output (outs, Yices2.assertProp prop)
                val _ = TextIO.output (outs, "(check)\n")
                val _ = TextIO.output (outs, "(show-model)\n")
            in
                ()
            end
    in
        case Yices2.runSolver lpqoTerminationInquiry of
            SOME assig =>
            let
                val _ = print "\n"
                val _ = L.app (fn (f,x) => print (f ^ ":" ^ (Int.toString (valOf (AL.find (Yices2.prArith x) assig))) ^ "\n")) table
            in true
            end
          | NONE => false
    end
        
end (* of local *)
end (* of struct *)
