(* file: dc.sml *)
(* description: divergence critic *)
(* author: Hiroto Kato *)

signature DC =
sig 
    val dc: Comp.rule * Comp.rule -> Term.fun_key list -> Comp.rules
    val dc1: Comp.rule * Comp.rule -> Comp.rules
end

structure Dc: DC =
struct

local
    structure L = List
    structure LP = ListPair
    structure LU = ListUtil
    structure AL = AssocList
    structure T = Term
in

exception noDifferenceMatch

(* divergence critic *)
(* we apply difference matching for (l1->r1), (l2->r2), generate lemmas *)
fun dc ((l1,r1),(l2,r2)) cfuns =
    let
        val term = T.fromString "?hole" (* hole *)
        val hole = (T.makeContext term nil, T.makeContext term nil, term)
        fun wavehole (c1,c2,r) = r
        fun skel (c1,c2,r) = c1 r
        fun erase (c1,c2,r) = c1 (c2 r)
        fun delsigma (c1,c2,r,sigma) = (c1,c2,r)
                                           
        fun decompose (t,u) cfuns = if T.root t = T.root u andalso LU.member (T.root t) (T.toSymbol cfuns)
                                    then L.concat (L.map (fn x => decompose x cfuns) (LP.map (fn (x,y) => (x,y)) (T.args t, T.args u)))
                                    else [(t,u)]

        fun mainDecompose ts cfuns = L.concat (L.map (fn (x,y) => decompose (x,y) cfuns) ts)
                                              
        fun delete nil = nil
          | delete ((l,r)::ts) = if l=r then delete ts
                                 else (l,r)::(delete ts)
             
        (* the size of a position*)
        fun size (t1,t2) = L.length (T.termMatchPosition t1 t2)
        fun unionC ([],ys) term = ys
          | unionC (((c1,c2,t)::xs),ys) term =
            let
                fun memberCont ((c1,c2,t),ys) t1 = List.exists (fn (c1',c2',t') => (c1 t1, c2 t1, t) = (c1' t1, c2' t1, t')) ys
                fun addCont ((c1,c2,t), ys) t1 = if memberCont ((c1,c2,t), ys) t1 then ys else L.rev ([(c1,c2,t)]@ys)
            in
                if memberCont ((c1,c2,t),ys) term  then unionC (xs,ys) term
                else unionC (xs, addCont ((c1,c2,t), ys) term) term
            end
        
        (* maximal difference matching *)
        fun MaxDm nil nil = [hole]
          | MaxDm nil ts = ts
          | MaxDm (x::xs) nil = MaxDm xs [x]
          | MaxDm ((c1,c2,r)::xs) (ts as ((c1',c2',r')::ys)) = if size (erase (c1,c2,r), (c2 r)) = size (erase (c1',c2',r'), (c2' r'))
                                                               then MaxDm xs (unionC (ts@[(c1,c2,r)],nil) term)
                                                               else (if (size (erase (c1,c2,r) ,(c2 r))) < (size (erase (c1',c2',r'), (c2' r')))
                                                                     then MaxDm xs [(c1,c2,r)]
                                                                     else MaxDm xs ts)
        (* delete no difference matching   *)
        fun deleteNoDm ts =
            let
                val d = case (L.filter (fn t1 => not(erase t1 = wavehole t1)) ts) of 
                            nil => [hole]
                          | x => x
            in
                d
            end

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
                val intpt = LU.union ((LU.intersection (ptl,ptr)), (L.map (fn x=>wavehole x) dimatch))

                (* (primaryTerm,variable)のpairを作る *)
                val table = LP.zip (intpt,alphVar) 
             
                (* デバック用 *)
                (* val _ = L.map (fn (x,y) => print ("(" ^ (T.toString x) ^ "," ^ (T.toString y) ^ ")\t")) table
                   val _ = print "\n"*)
            in
                gen (l,r) table
            end
                
        (* petering out heuristics or cancellation heuristics *)
        (* if (c1',c2',r') = hole then petering out else cancellation *)
        fun makerule (c1,c2,r) (c1',c2',r') = if (c1 (c2 r) = r) andalso (c1' (c2' r') = r')
                                              then (r,r') 
                                              else (if erase (c1',c2',r') = r'
                                                    then (erase (c1,c2,r), c1 r)
                                                    else (erase (c1,c2,r), c1' (c2' (c1 r))))

        (* Transverse Wave Rules *)
        (* fertilization heuristics or simplification heuristics*)
        fun twRules (t1 as (c1,c2,r)) (t2 as (c1',c2',r')) = 
            let
                val rule1 = erase t1
                val rule2 = skel t1
                val mp1 = T.termMatchPosition rule1 (c2 r)
                val p1 = case L.filter (fn px => not(px=mp1)) (L.filter (fn p => L.length p = L.length mp1) (T.pos rule1)) of
                             nil => raise noDifferenceMatch
                           | position => position
           
                val subt = L.map (fn p => ((T.subterm rule1 p),p)) p1 (*G(U0,"Acc")*)
                val context1 = L.map (fn x => T.makeContext rule2 x) p1
                val dmx = LP.map (fn (c,(st,p)) => (c,T.makeContext term nil,st)) (context1, subt)
                val rules1 = L.map (fn dm0 => generalization (rule1,erase dm0) [dm0]) dmx
                val insrules = L.concat (L.map (fn dm0 => (LP.map (fn ((l,r),(st,p)) => generalization (l,(T.makeContext r p (c2' (T.subterm r p)))) [dm0]) (rules1,subt))) dmx)
                val _ = print "twRules\n"
                val _ = print (Trs.prRules rules1)
                val _ = print (Trs.prRules insrules)
            in
                insrules
            end
                
        (* ********************** main************************ *)
        val rule1 = delete (mainDecompose [(l1,r1)] cfuns)
        val rule2 = delete (mainDecompose [(l2,r2)] cfuns)
        val table1 = LP.map (fn ((x1,y1),(x2,y2)) => (x1,x2)) (rule1,rule2)
        val table2 = LP.map (fn ((x1,y1),(x2,y2)) => (y1,y2)) (rule1,rule2)
                            
        (* difference matching of lhs *)                            
        val dmleft1 = deleteNoDm (L.map (fn x => delsigma x) (Subst.difMatch (l1,l2)))
        (* maximal difference matching of left hand *)                                 
        val dml1 = deleteNoDm (MaxDm dmleft1 nil)  
        val dmleft2 = L.map (fn (l1,l2) => deleteNoDm (L.map (fn x => delsigma x) (Subst.difMatch (l1,l2)))) table1
        val dml2 = L.concat (L.map (fn x => deleteNoDm (MaxDm x nil)) dmleft2)
        (* difference matching of rhs *)                                
        val dmright1 = deleteNoDm (L.map (fn x => delsigma x) (Subst.difMatch (r1,r2)))
        (* maximal difference matching of right hand *)
        val dmr1 = deleteNoDm (MaxDm dmright1 nil)  
        val dmright2 = L.map (fn (r1,r2) => deleteNoDm (L.map (fn x => delsigma x) (Subst.difMatch (r1,r2)))) table2
        val dmr2 = L.concat (L.map (fn x => deleteNoDm (MaxDm x nil)) dmright2)

        (* デバック用 *)
        (* val _ = print (Trs.prRules (rule1@rule2))
        (* difference matching of lhs *)
        val _ = print "difference Match of left hand side \n"
        (* val _ = L.map (fn x => Subst.dmToString x) dmleft2 *)
        val _ = Subst.dmToString dml2        
        
        (* difference matching of rhs *)
        val _ = print "difference Match of right hand side \n"
        (* val _ = L.map (fn x => Subst.dmToString x ) dmright2*)
        val _ = Subst.dmToString dmr2 *)        

        val rules = L.concat (LP.map (fn (dml,dmr) => if (skel dml = wavehole dml)
                                                      then [makerule dmr dml]
                                                      else [makerule dml dmr]) (dml2,dmr2))
        val rules1 = []
        val lemmas = delete ((LP.map (fn (rule,dml) => generalization rule [dml]) (rules,dml1))@rules1)
        (* デバック *)        
        (* val _ = print "lemmas after generalization \n"     
           val _ = print (Trs.prRules lemmas)
           val _ = print "*************************************************************************\n" *)

    in
        if L.exists (fn rule => Trs.isTrs rule) lemmas then lemmas
        else rules 
    end


(* ************************************************************************************************************************************  *)
        
(*no cfuns version*)
fun dc1 ((l1,r1),(l2,r2)) =
    let
        val term = T.fromString "?hole" (* hole *)
        val hole = (T.makeContext term nil, T.makeContext term nil, term)
        fun wavehole (c1,c2,r) = r
        fun skel (c1,c2,r) = c1 r
        fun erase (c1,c2,r) = c1 (c2 r)
        fun delsigma (c1,c2,r,sigma) = (c1,c2,r)
           
        (* the size of a position*)
        fun size (t1,t2) = L.length (T.termMatchPosition t1 t2)
        fun unionC ([],ys) term = ys
          | unionC (((c1,c2,t)::xs),ys) term =
            let
                fun memberCont ((c1,c2,t),ys) t1 = List.exists (fn (c1',c2',t') => (c1 t1, c2 t1, t) = (c1' t1, c2' t1, t')) ys
                fun addCont ((c1,c2,t), ys) t1 = if memberCont ((c1,c2,t), ys) t1 then ys else L.rev ([(c1,c2,t)]@ys)
            in
                
                if memberCont ((c1,c2,t),ys) term  then unionC (xs,ys) term
                else unionC (xs, addCont ((c1,c2,t), ys) term) term
            end
        
        (* maximal difference matching: (Term.Context * Term.Context * Term.term) list -> (Term.Context * Term.Context * Term.term) list -> (Term.Context * Term.Context * Term.term) list *)
        fun MaxDm nil nil = [hole]
          | MaxDm nil ts = ts
          | MaxDm (x::xs) nil = MaxDm xs [x]
          | MaxDm ((c1,c2,r)::xs) (ts as ((c1',c2',r')::ys)) = if size (erase (c1,c2,r), (c2 r)) = size (erase (c1',c2',r'), (c2' r'))
                                                               then MaxDm xs (unionC (ts@[(c1,c2,r)],nil) term)
                                                               else (if (size (erase (c1,c2,r) ,(c2 r))) < (size (erase (c1',c2',r'), (c2' r')))
                                                                     then MaxDm xs [(c1,c2,r)]
                                                                     else MaxDm xs ts)
        (* delete no difference matching : (Term.Context * Term.Context * Term.term) list -> (Term.Context * Term.Context * Term.term) list *)
        fun deleteNoDm ts =
            let
                val d = case (L.filter (fn t1 => not(erase t1 = wavehole t1)) ts) of 
                            nil => [hole]
                          | x => x
            in
                d
            end

        (* main *)
        (* difference matching of lhs *)
        val dmleft1 = deleteNoDm (L.map (fn x => delsigma x) (Subst.difMatch (l1,l2)))
        (* maximal difference matching of lhs *)
        val dml1 = deleteNoDm (MaxDm dmleft1 nil)
        (* difference matching of rhs *) 
        val dmright1 = deleteNoDm (L.map (fn x => delsigma x) (Subst.difMatch (r1,r2)))
        (* maximal difference matching of rhs *)                                  
        val dmr1 = deleteNoDm (MaxDm dmright1 nil)

        (* デバック用 *)
        (* difference matching of lhs *)                              
        (* val _ = print (Trs.prRules [(l1,r1),(l2,r2)])
        (* difference matching of lhs *)
        val _ = print "difference Match of left hand side \t"
        val _ = Subst.dmToString dml1
        (* difference matching of rhs *)
        val _ = print "difference Match of right hand side\t"
        val _ = Subst.dmToString dmr1 *)

        (* generalization heuristics *)
        fun generalization (l,r) dimatch =
            let
                (* string alphabet list little:97~122 big:65~90 *)
                fun alphlist 90 = [str (chr 90)]
                  | alphlist n = [str (chr n)]@(alphlist (n+1))
                (* variable list *) 
                val varsl = L.map (fn x => T.fromString ("?" ^ (Var.toString x))) (T.vars l)
                val varsr = L.map (fn x => T.fromString ("?" ^ (Var.toString x))) (T.vars r)
                (* variable list of string other than the variable used for l -> r *)
                val alphVar = LU.diff (L.map (fn str => T.fromString ("?" ^ str)) (alphlist 65), LU.union (varsl, varsr))
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
                val intpt = LU.union ((LU.intersection (ptl,ptr)), (L.map (fn x=>wavehole x) dimatch))

                (* we generate the pair of (primaryTerm,variable) *)                                     
                val table = LP.zip (intpt,alphVar) 
             
                (* デバック用 *)
                (* val _ = L.map (fn (x,y) => print ("(" ^ (T.toString x) ^ "," ^ (T.toString y) ^ ")\t")) table
                   val _ = print "\n"*)
            in
                gen (l,r) table
            end
      
        (* petering out heuristics or cancellation heuristics *)
        (* if (c1',c2',r') = hole then petering out else cancellation *)
        fun makerule (c1,c2,r) (c1',c2',r') = if (c1 (c2 r) = r) andalso (c1' (c2' r') = r')
                                              then (r,r') 
                                              else (if erase (c1',c2',r') = r'
                                                    then (erase (c1,c2,r), c1 r)
                                                    else (erase (c1,c2,r), c1' (c2' (c1 r))))
                 
        (* Transverse Wave Rules *)
        (* fertilization heuristics or simplification heuristics*)
        fun twRules_backup (t1 as (c1,c2,r)) (t2 as (c1',c2',r')) = 
            let
                val _ = print "\t twRules\n"
                val rule1 = erase t1
                val rule2 = skel t1
                val mp1 = T.termMatchPosition rule1 (c2 r)
                val p1 = case L.filter (fn px => not(px=mp1)) (L.filter (fn p => L.length p = L.length mp1) (T.pos rule1)) of
                             nil => raise noDifferenceMatch
                           | position => position
                                             
                val subt = L.map (fn p => (T.subterm rule1 p)) p1
                val context1 = L.map (fn x => T.makeContext rule2 x) p1
                val dmx = LP.map (fn (c,st) => (c, c2',st)) (context1,subt)
            in
                L.map (fn dm0 => (rule1,erase dm0)) dmx
            end
      
        fun twRules (t1 as (c1,c2,r)) (t2 as (c1',c2',r')) = 
            let
                val _ = print "\t twRules\n"
                val rule1 = erase t1
                val rule2 = skel t1
                val mp1 = T.termMatchPosition rule1 (c2 r)
                val p1 = case L.filter (fn px => not(px=mp1)) (L.filter (fn p => L.length p = L.length mp1) (T.pos rule1)) of
                             nil => raise noDifferenceMatch
                           | position => position
           
                val subt = L.map (fn p => ((T.subterm rule1 p),p)) p1 (*G(U0,"Acc")*)
                val context1 = L.map (fn x => T.makeContext rule2 x) p1
           
                val dmx = LP.map (fn (c,(st,p)) => (c,T.makeContext term nil,st)) (context1, subt)
                val rules1 = L.map (fn dm0 => generalization (rule1,erase dm0) [dm0]) dmx
                val _ = print (Trs.prRules rules1)
                val insrules = L.concat (L.map (fn dm0 => (LP.map (fn ((l,r),(st,p)) => generalization (l,(T.makeContext r p (c2' (T.subterm r p)))) [dm0]) (rules1,subt))) dmx)
                val _ = print (Trs.prRules insrules)   
            in
                insrules
            end      
      
        val rules = L.concat (L.map (fn dml => L.concat (L.map (fn dmr => [makerule dml dmr]) dmr1)) dml1)
        val rules1 = (L.concat (L.map (fn dml => L.concat (L.map (fn dmr=> (if (L.length (T.args (erase dml)) = 1) andalso (skel dml = wavehole dml)
                                                                            then []
                                                                            else twRules dml dmr)) dmr1)) dml1))
        val lemmas = (LP.map (fn (rule,dml) => generalization rule [dml]) (rules,dml1))@rules1
                        
        (* デバック用 *)
        (* val _ = print "lemmas"     
           val _ = print (Trs.prRules lemmas)
           val _ = print ""*)
    in
        lemmas
    end

end (* of local *)

end
