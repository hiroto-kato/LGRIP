(* file: dc_ms.sml *)
(* description: divergence critic in ManySorted *)
(* author: Hiroto Kato *)

signature DCMS =
sig 
    val dcMs: ManySorted.ms_rule * ManySorted.ms_rule -> ManySorted.ms_sign * Term.fun_key list -> ManySorted.ms_rules
end

structure DcMs: DCMS =
struct

local
    structure L = List
    structure LP = ListPair
    structure LU = ListUtil
    structure AL = AssocList
    structure T = Term
    structure MS = ManySorted
in

exception noDifferenceMatch

(* divergence critic *)
(* we apply difference matching for (l1->r1:ty1), (l2->r2:ty2), generate lemmas *)
fun dcMs (((l1,r1),ty1),((l2,r2),ty2)) (sign,cfuns) =
    let
        fun generalization (l,r) dimatch =
            let
                (* string alphabet list little:97~122 big:65~90 *)
                fun alphlist 122 = [str (chr 122)]
                  | alphlist n = [str (chr n)]@(alphlist (n+1))
                (* variable and function list *) 
                val varsl = L.map (fn x => T.fromString ("?" ^ (Var.toString x))) (T.vars l)
                val varsr = L.map (fn x => T.fromString ("?" ^ (Var.toString x))) (T.vars r)
                val funsl = L.map (fn x => T.fromString ("?" ^ (Fun.toString x))) (T.funs l)
                val funsr = L.map (fn x => T.fromString ("?" ^ (Fun.toString x))) (T.funs l)
                (* variable list of string other than the variable used for l -> r *)       
                val alphVar = LU.diff (L.map (fn str => T.fromString ("?" ^ str)) (alphlist 97), LU.union (varsl@varsr@funsl@funsr,nil))
                (* we generate C[t] from (term,poslist,t) *)
                fun makeContexts term nil t = T.fillContext (T.makeContext term nil) term
                  | makeContexts term (x::xs) t = makeContexts (T.fillContext (T.makeContext term x) t) xs t
                (* we generalize l->r based on given table *)(* some bugs *)
                fun gen (l0,r0) ((t,v)::nil) = (makeContexts l0 (T.termMatchpos l0 t) v, makeContexts r0 (T.termMatchpos r0 t) v)
                  | gen (l0,r0) ((t,v)::xs) = gen (makeContexts l0 (T.termMatchpos l0 t) v, makeContexts r0 (T.termMatchpos r0 t) v) (L.map (fn (x,y) => (makeContexts x (T.termMatchpos x t) v, y)) xs)

                (* primary term heuristic *)
                (* subtermList *)
                val subl = L.map (fn p => (T.subterm l p)) (T.pos l)
                val subr = L.map (fn p => (T.subterm r p)) (T.pos r)
                (* delete non-recursive argument positions to functions *)
                val ptl = L.filter (fn term => not(T.nonrec term)) (L.filter (fn t => not(L.exists (fn x => x=t) varsl)) subl)
                val ptr = L.filter (fn term => not(T.nonrec term)) (L.filter (fn t => not(L.exists (fn x => x=t) varsr)) subr)

                (* intersection of primary terms and the wave-holes*)
                val intpt = LU.union ((LU.intersection (ptl,ptr)), (L.map (fn x=>Dm_ms.wavehole x) dimatch))

                (* we generate the pair of (primaryTerm,variable) *)
                val table = LP.zip (intpt,alphVar) 
                (* デバック用 *)
                (* val _ = L.map (fn (x,y) => print ("(" ^ (T.toString x) ^ "," ^ (T.toString y) ^ ")\t")) table *)
                (* val _ = print "\n"*)
            in
                gen (l,r) table
            end
        (* petering out heuristics or cancellation heuristics *)
        (* if (c1',c2',r') = hole then petering out else cancellation *)
        fun makerule (c1,c2,r) (c1',c2',r') = if (c1 (c2 r) = r) andalso (c1' (c2' r') = r') then (r,r') (*raise noDifferenceMatch*)
                                              else (if Dm_ms.erase (c1',c2',r') = r' then (Dm_ms.erase (c1,c2,r), c1 r) 
                                                    else (Dm_ms.erase (c1,c2,r), c1' (c2' (c1 r))))

        fun makeGrule (c1,c2,r) (c1',c2',r') =
            let
                val vl = LU.union (T.vars (c1 (c2 r)),T.vars (c1' (c2' r')))
                val max = L.foldr (fn ((x,i),n) => Int.max (i,n)) 0 vl
                val genterm0 = if T.isGround r then r else T.Var ("x",max+1)
                val genterm = T.Var ("x",max+1)
            in
                if (c1 (c2 r) = r) andalso (c1' (c2' r') = r') then (r,r')
                else (if Dm_ms.erase (c1',c2',r') = r' then (Dm_ms.erase (c1,c2,genterm), c1 genterm)
                      else (Dm_ms.erase (c1,c2,genterm), c1' (c2' (c1 genterm))))
            end
        fun decompose ts (sign,cfuns) = 
            let
                fun mainDecompose ((t,u),ty) =
                    if T.isFun t then
                        if T.root t = T.root u andalso LU.member (T.root t) (T.toSymbol cfuns)
                        then (let
                                 val tylist =
                                     case MS.sortInferenceStep sign [(t,ty)] of
                                         NONE => nil
                                       | SOME xs => xs
                                 val rs = LP.map (fn (x,y) => (x,y)) (T.args t, T.args u)
                                 val msrs = L.mapPartial (fn (l,r) => case AL.find l tylist of
                                                                          NONE => NONE
                                                                        | SOME ty0 => SOME ((l,r),ty0)) rs
                             in
                                 L.concat (L.map (fn x => mainDecompose x) msrs)
                             end)
                        else [((t,u),ty)]
                    else
                        [((t,u),ty)]
            in
                L.filter (fn ((s,t),ty) => not(s=t)) (L.concat (L.map (fn ((x,y),ty) => mainDecompose ((x,y),ty)) ts))
            end

        fun delete nil = nil
          | delete ((l,r)::ts) = if l=r then delete ts
                                 else (l,r)::(delete ts)
        fun deleteMs nil = nil
          | deleteMs (((l,r),ty)::ts) = if l=r then deleteMs ts
                                        else ((l,r),ty)::(deleteMs ts)
        fun toMsRule sign (l,r) =
            let
                val sort = AL.find (Fun.fromString (Symbol.toString (T.root l))) sign
                val rule = case sort of
                               NONE => NONE
                             | SOME (sortlist,sortkey) => SOME ((l,r),sortkey)
            in
                rule
            end

        (* ********************** main ************************ *)
        val rule1 = deleteMs (decompose [((l1,r1),ty1)] (sign,cfuns))
        val rule2 = deleteMs (decompose [((l2,r2),ty2)] (sign,cfuns))
        val table1 = LP.map (fn (((x1,y1),ty1),((x2,y2),ty2)) => ((x1,x2),ty2)) (rule1,rule2)
        val table2 = LP.map (fn (((x1,y1),ty1),((x2,y2),ty2)) => ((y1,y2),ty2)) (rule1,rule2)

        (* difference matching of lhs *)
        val dmleft1 = L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((l1,ty1),(l2,ty2)))
        (* maximal difference matching of lhs *)
        val dml1 = Dm_ms.MaxDm dmleft1 nil
        val dmleft2 = L.map (fn ((l1,l2),ty) => Dm_ms.deleteNoDm (L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((l1,ty),(l2,ty))))) table1
        val dml2 = L.concat (L.map (fn x => Dm_ms.deleteNoDm (Dm_ms.MaxDm x nil)) dmleft2)
        (* difference matching of rhs *)      
        val dmright1 = L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((r1,ty1),(r2,ty2)))
        (* maximal difference matching of rhs *)
        val dmr1 = Dm_ms.MaxDm dmright1 nil
        val dmright2 = L.map (fn ((r1,r2),ty) => Dm_ms.deleteNoDm (L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((r1,ty),(r2,ty))))) table2
        val dmr2 = L.concat (L.map (fn x => Dm_ms.deleteNoDm (Dm_ms.MaxDm x nil)) dmright2)

        val rules = LP.map (fn (dml,dmr) => if (Dm_ms.skel dml = Dm_ms.wavehole dml) then makerule dmr dml
                                            else makerule dml dmr) (dml1,dmr1)

        val lemmasx = delete (LP.map (fn (dml,dmr) => if (Dm_ms.skel dml = Dm_ms.wavehole dml) then makeGrule dmr dml
                                                      else makeGrule dml dmr) (dml1,dmr1))
        val lemmas = delete (LP.map (fn (rule,dml) => generalization rule [dml]) (rules,dml1))

        (* デバック用 *)
        (*val _ = Subst.dmToString dml1
          val _ = Subst.dmToString dmr1
          val _ = print (Trs.prRules lemmasx)
          val _ = print (Trs.prRules lemmas)*)
    in
        if L.exists (fn rule => Trs.isTrs rule) lemmasx then L.mapPartial (fn lr => toMsRule sign lr) lemmasx
        else L.mapPartial (fn lr => toMsRule sign lr) rules 
    end
end (* of local *)
end

(* 
val sign = List.map (fn x => ManySorted.rdMsFun x) ["+:Nat,Nat -> Nat","s:Nat->Nat","0:Nat","even:Nat->Bool","true:Bool","false:Bool","qrev:List,List->List","cons:Nat,List->List","nil:List"];
val rs1 = (Trs.rdRule "even(+(?x,?x)) -> true", ManySorted.rdSort "Bool");
val rs2 = (Trs.rdRule "even(+(?x_2,s(s(?x_2)))) -> true",ManySorted.rdSort "Bool");
val rs1 = (Trs.rdRule "qrev(qrev(?xs_1,cons(?x_1,nil)),nil) -> cons(?x_1,?xs_1)", ManySorted.rdSort "List");
val rs2 = (Trs.rdRule "qrev(qrev(?xs_2,cons(?x_2,cons(?x_1,nil))),nil) -> cons(?x_1,cons(?x_2,?xs_2))",ManySorted.rdSort "List");
val cfuns = List.concat (List.map (fn x => Term.funs x) (List.map (fn x => Term.fromString x) ["cons","s","0","nil","true","false"]));
val lem = DcMs.dcMs (rs1,rs2) (sign,cfuns);

*)
