(* file: lem_gen.sml *)
(* lemma generation system based on Rewriging Induction *)
(* author: Hiroto Kato*)

signature LEMGEN =
sig
    val expd: ManySorted.ms_rules -> ManySorted.ms_rule -> Term.context * Term.term -> ManySorted.ms_rules
    val expand: (Term.fun_key list * Term.fun_key list) * ManySorted.ms_rules * (Trs.rule -> bool) -> (ManySorted.ms_eqs * ManySorted.ms_rules) -> ManySorted.ms_eqs * ManySorted.ms_rules
    val simplify: ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs * ManySorted.ms_rules -> ManySorted.ms_eqs * ManySorted.ms_rules
    val delete: ManySorted.ms_eqs * ManySorted.ms_rules -> ManySorted.ms_eqs * ManySorted.ms_rules
    val decompose: ManySorted.ms_sign * Term.fun_key list -> ManySorted.ms_eqs *ManySorted.ms_rules -> ManySorted.ms_eqs * ManySorted.ms_rules
    val decompose0: ManySorted.ms_eqs -> ManySorted.ms_sign * Term.fun_key list -> ManySorted.ms_eqs
    val findSeq: (Subst.dmset * Subst.dmset) -> ManySorted.ms_rules ->  ManySorted.ms_rules
    val postulate: ManySorted.ms_rules -> ManySorted.ms_rules -> (ManySorted.ms_sign * Term.fun_key list * Term.fun_key list) -> ManySorted.ms_rules
    val postulatePrint: ManySorted.ms_rules -> ManySorted.ms_rules -> (ManySorted.ms_sign * Term.fun_key list * Term.fun_key list) -> ManySorted.ms_rules
    val lemGenStep: (Term.fun_key list * Term.fun_key list * ManySorted.ms_sign) * ManySorted.ms_rules * (Trs.rule -> bool) -> (ManySorted.ms_eqs * ManySorted.ms_rules) -> ManySorted.ms_eqs * ManySorted.ms_rules
    val lemGen: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> ManySorted.ms_eqs
    val lemGenPrint: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> ManySorted.ms_eqs
    val randLemGenDef: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> ManySorted.ms_eqs
    val randLemGenDefPrint: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> ManySorted.ms_eqs
    val randLemGenDepth: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> int -> ManySorted.ms_eqs
    val randLemGenDepthPrint: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> int -> ManySorted.ms_eqs
    val DivCritic: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> ManySorted.ms_eqs
    val DmNewLem: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> ManySorted.ms_eqs 
end 

structure LemGen:LEMGEN = 
struct

local 
    structure L = List
    structure AL = AssocList
    structure LP = ListPair
    structure LU = ListUtil
    structure T = Term
    structure MS = ManySorted
in

exception Failure
exception Success
exception Stopped
exception noLemmas

fun expd rs ((s,t),ty) (C,u) =
    let
        val rs2 = L.map (fn (l,r) => Trs.renameRules (LU.union ((T.vars s), (T.vars t))) (l,r)) (MS.dropSortInMsRules rs)
    in
        L.mapPartial (fn (l,r) =>
                         case Subst.unify (u,l) of
                             SOME sigma => SOME ((Subst.apply sigma (C r), (Subst.apply sigma t)),ty)
                           | NONE => NONE ) rs2
    end        
        
fun expand ((dfuns,cfuns),rs,grter) (es,hs) =
    let
        (* select directable equation of smallest size *)
        fun size ((s,t),ty) = L.length (T.pos s) + L.length (T.pos t)
        fun check ((s,t),ty) = if grter (s,t) then SOME ((s,t),ty)
                               else if grter (t,s) then SOME ((t,s),ty)
                               else SOME ((s,t),ty)

        fun select nil = NONE
          | select xs = case (L.mapPartial (fn x => check x) xs) of
                            nil => NONE
                          | rules => SOME rules

        fun removeEq rs es = LU.diff (es,rs@(L.map (fn ((s,t),ty) => ((t,s),ty)) rs))
                                     
        fun selectAndExpand es0 =
            case select es0 of 
                SOME rules => (case (L.concat (L.map (fn ((s,t),ty) =>
                                                         case T.findBasicSubtermLiOc (dfuns,cfuns) s of
                                                             SOME cu => expd rs ((s,t),ty) cu
                                                           | NONE => []) rules)) of
                                   nil => NONE
                                 | xs => SOME (xs,rules))
              | NONE => NONE
                            
        val invh = L.map (fn ((s,t),ty) => ((t,s),ty)) hs
        val rs1 = LU.union (hs,invh)
        val (expdu1,rules1) = case selectAndExpand es of
                                  SOME (expdu,rules) => (L.map (fn ((s,t),ty) => ((Rewrite.linfOrder (MS.dropSortInMsRules rs1,grter) s,t),ty)) expdu,rules)
                                | NONE => (print "Ind.expand: equation to expand\n";raise Failure)
                                              
    in
        (LU.union (expdu1@(removeEq rules1 es),nil) , ListMergeSort.sort (fn (s,t) => size s < size t) (LU.union (rules1@hs,nil)))
    end

fun simplify (rs,grter) (es,hs) =
    let
        fun check (s,t) = if grter (s,t) then SOME (s,t)
                          else if grter (t,s) then SOME (t,s)
                          else SOME (t,s)
                                    
        fun isNFOrderC rh hih term = case Rewrite.listepOrder (rh,grter) term
                                      of NONE => (case Rewrite.listepOrder (hih,grter) term
                                                   of NONE => true
                                                    | _  => false)
                                       | _ => false
                                                  
        fun linfOrderC rh hih term = case isNFOrderC rh hih term of
                                         true => term
                                       | false => case Rewrite.listepOrder (rh,grter) term of
                                                      SOME t => linfOrderC rh hih (Rewrite.linfOrder (hih,grter) t)
                                                    | NONE => linfOrderC rh hih (Rewrite.linfOrder (hih,grter) term)
        val rs1 = MS.dropSortInMsRules (LU.union (rs,hs))
        val invhs = L.map (fn ((s,t),ty) => ((t,s),ty)) hs
        val rs2 = MS.dropSortInMsRules (LU.union (hs,invhs))
    in
        (L.map (fn ((l,r),ty) => ((linfOrderC rs1 rs2 l,linfOrderC rs1 rs2 r),ty)) es,hs)
    end

fun delete (es,hs) =
    let
        fun func1 nil ys = ys
          | func1 (x::xs) ys= case L.exists (fn t => Trs.equal (MS.dropSortInMsRule x) (MS.dropSortInMsRule t)) xs of
                                  true => func1 xs ys
                                | false => func1 xs (ys@[x])
        val es0 = func1 es nil
        val hs0 = func1 hs nil
        val es1 = L.filter (fn ((l,r),ty) => not(case Rewrite.listep (MS.dropSortInMsRules hs0) l of
                                                     SOME t => t=r
                                                   | NONE => l=r)
                                             orelse not(case Rewrite.listep (MS.dropSortInMsRules hs0) r of
                                                            SOME t => t=l
                                                          | NONE => l=r)) es0
    in
        ((L.filter (fn ((x,y),ty) => not(x=y)) es1),hs0)
    end

fun decompose (sign,cfuns) (es,hs) = 
    let
        fun mainDecompose ((t,u),ty) =
            if T.isFun t then
                if T.root t = T.root u andalso LU.member (T.root t) (T.toSymbol cfuns)
                then (let
                         val tylist = case MS.sortInferenceStep sign [(t,ty)] of
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
            else [((t,u),ty)]
    in
        (L.concat (L.map (fn ((x,y),ty) => mainDecompose ((x,y),ty)) es),hs)
    end

(* we search rules like D[C[u]]=D'[C[u]] from hs (search divergence series) *)
fun findSeq (_,_) nil = nil
  | findSeq (ds1,ds2) hs =
    let
        fun findSeq1 (_,_) nil _ = nil
          | findSeq1 (ls,rs) (((l,r),ty)::hs1) hs2 = 
            case (ds1,ds2,ls,rs) of
                (nil,nil,_,_) => nil
              | ((c1,c2,t)::xs,nil,(cl,cl',tl)::xs',nil) =>
                let 
                    val l0 = cl (cl' tl)
                    val context1 = T.makeContext (c2 (cl' t)) (T.termMatchPosition (c2 (cl' t)) t)
                    val dm1 = [(c1,context1,t)]
                in
                    if (Trs.equal (l,r) (l0,r)) orelse (Trs.equalTerm l l0) then 
                        ((l,r),ty)::(findSeq1 (dm1,ds2) (LU.diff (hs2,[((l,r),ty)])) (LU.diff (hs2,[((l,r),ty)])) )
                    else findSeq1 (ls,rs) hs1 hs2
                end
              | (nil,(c1',c2',t')::ys,nil,(cr,cr',tr)::ys') => 
                let 
                    val r0 = cr (cr' tr)
                    val context2 = T.makeContext (c2' (cr' t')) (T.termMatchPosition (c2' (cr' t')) t')
                    val dm2 = [(c1',context2,t')]
                in
                    if (Trs.equal (l,r) (l,r0)) orelse (Trs.equalTerm r r0) then 
                        ((l,r),ty)::(findSeq1 (ds1,dm2) (LU.diff (hs2,[((l,r),ty)])) (LU.diff (hs2,[((l,r),ty)])) )
                    else findSeq1 (ls,rs) hs1 hs2
                end
              | ((c1,c2,t)::xs,(c1',c2',t')::ys,(cl,cl',tl)::xs',(cr,cr',tr)::ys') => 
                let
                    val l0 = cl (cl' tl)
                    val r0 = cr (cr' tr)
                    val (dl,dr) = Dm_ms.renameDm (ls,rs)
                    val context1 = T.makeContext (c2 (cl' t)) (T.termMatchPosition (c2 (cl' t)) t)
                    val context2 = T.makeContext (c2' ( cr' t')) (T.termMatchPosition (c2' (cr' t')) t')
                    val dm1 = [(c1,context1,t)]
                    val dm2 = [(c1',context2,t')]
                in
                    if (Trs.equal (l,r) (l0,r0)) orelse (Trs.equalTerm l l0 andalso Trs.equalTerm r r0) then 
                        ((l,r),ty)::(findSeq1 (dm1,dm2) (LU.diff (hs2,[((l,r),ty)])) (LU.diff (hs2,[((l,r),ty)])))
                    else findSeq1 (ls,rs) hs1 hs2
                end
    in
        findSeq1 (ds1,ds2) hs hs 
    end

fun decompose0 ts (sign,cfuns) = 
    let
        fun mainDecompose ((t,u),ty) =
            if T.isFun t then
                if T.root t = T.root u andalso LU.member (T.root t) (T.toSymbol cfuns)
                then (let
                         val tylist = case MS.sortInferenceStep sign [(t,ty)] of
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
            else [((t,u),ty)]
    in
        L.filter (fn ((s,t),ty) => not(s=t)) (L.concat (L.map (fn ((x,y),ty) => mainDecompose ((x,y),ty)) ts))
    end

(* we take specified length from the list from the topリストから指定した長さを上から取ってくる *)
fun listlen 0 (xl,sl) = L.rev sl
  | listlen n (x::xl,sl) = if xl=nil then L.rev (x::sl)
                           else listlen (n-1) (xl, x::sl)
                                        
(* Extraction of Divergence Sequences *)
fun extract nil _ (sign,cfuns,dfuns) = nil
  | extract hs0 xs (sign,cfuns,dfuns) =
    let
        (* select the rule of smallest size *)
        fun size ((s,t),ty) = L.length (T.pos s) + L.length (T.pos t)
        (* we select the ground basic term *)
        fun selectGBasic nil = NONE
          | selectGBasic (((l,r),ty)::hs1) = if L.exists (fn x => LU.member x cfuns) (T.funs r)
                                             then selectGBasic hs1
                                             else SOME [((l,r),ty)]
        (* we select the hierarchy term *)
        fun selectHierarchy nil = NONE
          | selectHierarchy (((l,r),ty)::hs1) = if T.isHierarchy (cfuns,dfuns) r
                                                then SOME [((l,r),ty)]
                                                else selectHierarchy hs1
        (* judgment of divergence sequence *)
        fun isNotDiv xs = (L.length xs) < 3
        (* function that we extract divergence sequences *)
        fun makeDiv1 (nil,nil) = raise Failure
          | makeDiv1 (nil,_) = nil
          | makeDiv1 (_,nil) = nil
          | makeDiv1 (rules,hsl) = 
            let
                val dfm = L.map (fn msrule => (msrule, Dm_ms.isDif sign msrule hsl)) rules
                val divseqx = L.concat (L.map (fn (msrule,(dmset1,dmset2)) => msrule::(findSeq (dmset1,dmset2) hsl)) dfm)
            in
                if L.length divseqx = 1 then nil
                else (if isNotDiv divseqx
                      then makeDiv1 (rules,LU.diff (hsl,LU.diff (divseqx,rules)))
                      else divseqx)
            end
                
        val hsx = LU.diff (hs0,xs)
        val simpRule = case selectGBasic hsx of
                           SOME ys => ys
                         | NONE => (case selectHierarchy hsx of
                                        SOME zs => zs
                                      | NONE => (if hsx=nil then nil else [L.hd hsx]))
                                       
        val hs2 = LU.diff (hs0,simpRule)
        val divl = makeDiv1 (simpRule,hs2)
        val rest = LU.diff (hs2,divl)
    in
        if simpRule = nil then [divl]
        else (if divl = nil then extract rest (xs@simpRule) (sign,cfuns,dfuns)
              else [divl]@(extract rest (xs@simpRule) (sign,cfuns,dfuns)))
    end
        
(* we select the sequence to which divergence critic can be applied *)
fun findDiv nil sign = nil
  | findDiv (x::xs) sign =
    let
        val term = T.fromString "?hole"
        val hole = (T.makeContext term nil, T.makeContext term nil, term)
        fun rside ((l,r),ty) = (r,ty)
        fun lside ((l,r),ty) = (l,ty)
        fun size (t1,t2) = L.length (T.termMatchPosition t1 t2)
        fun check xs = (Dm_ms.skel xs = Dm_ms.wavehole xs)
                           
        fun difop sign (s,t) = case Dm_ms.msDifMatch sign (s,t) of
                                   nil => NONE
                                 | zs => SOME (L.hd (Dm_ms.MaxDm (L.map (fn z => Dm_ms.delSigma z) zs) nil))
        val ys = listlen 2 (x,nil)
        val r1 = rside (L.hd ys)
        val r2 = rside (L.hd (L.tl ys))
        val l1 = lside (L.hd ys)
        val l2 = lside (L.hd (L.tl ys))
        val df = difop sign (r1,r2)
    in
        case df of
            SOME zs => if check zs then x::(findDiv xs sign)
                       else (case difop sign (l1,l2) of
                                 SOME ys => if check ys
                                            then (L.map (fn ((s,t),ty) => ((t,s),ty)) x)::(findDiv xs sign)
                                            else findDiv xs sign
                               | NONE => findDiv xs sign)
          | NONE => findDiv xs sign
    end

(* we exclude equations on both hand side *)
fun checkequal nil = nil
  | checkequal ((lr,ty)::rest) = if L.exists (fn lr0 => Trs.equal lr (MS.dropSortInMsRule lr0)) rest
                                 then checkequal rest
                                 else (lr,ty)::(checkequal rest)

(* lemma generation *)
fun postulate rs hs (sign,cfuns,dfuns) =
    let
        (* we apply the divergence critic *)
        fun divergenceCritic ((l,ty)::ls) =
            case L.length ls of
                0 => nil
              | _ => DcMs.dcMs ((l,ty),(L.hd ls)) (sign,cfuns)

        (* we apply the lemma generation based on difference matching and generalization *)
        fun newLemmaGeneralization (l::ls) =
            case L.length ls of
                0 => nil
              | _ => Lemma.lemmagen (l,L.hd ls) (sign,cfuns)

        val hs1 = L.rev (decompose0 hs (sign,cfuns))
        val divs = L.filter (fn x => not(x=nil)) (extract hs1 nil (sign,cfuns,dfuns))
        (* the set of hypotheses other than the divergence sequence discovered by extract *)
        val rest1 = LU.diff (hs1,(L.concat divs))   
        val divs1 = nil
        (* sequence the divergence critic can apply *)
        val dvl = findDiv (divs@divs1) sign
        (* sequence the divergence critic cannot apply *)                          
        val restOfDivs = LU.diff (LU.diff (divs@divs1,dvl),L.map (fn xs => (L.map (fn ((s,t),ty) => ((t,s),ty)) xs)) dvl) 
        (* divergence critic *)                                 
        val dcl = L.filter (fn ((l,r),ty) => not(l=r)) (L.concat (L.map (fn l => divergenceCritic l) dvl))
        (* lemma generation method based on generalization and difference matching *)
        val lem = L.filter (fn ((l,r),ty) => not(l=r)) (L.concat (L.map (fn l => newLemmaGeneralization l) divs)) 
        val checkeqs = checkequal (LU.union (dcl@lem,nil))
    in
        checkeqs
    end
        
(* lemma generation ~Debug Version~*)
fun postulatePrint rs hs (sign,cfuns,dfuns) =
    let
        fun divergenceCritic ((l,ty)::ls) =
            case L.length ls of
                0 => nil
              | _ => DcMs.dcMs ((l,ty),(L.hd ls)) (sign,cfuns)

        fun newLemmaGeneralization (l::ls) =
            case L.length ls of
                0 => nil
              | _ => Lemma.lemmagen (l,L.hd ls) (sign,cfuns)

        val hs1 = L.rev (decompose0 hs (sign,cfuns))
        val divs = L.filter (fn x => not(x=nil)) (extract hs1 nil (sign,cfuns,dfuns))
        (* the set of hypotheses other than the divergence sequence discovered by extract *)
        val rest1 = LU.diff (hs1,(L.concat divs))
        val divs1 = nil
        (* sequence the divergence critic can apply *)
        val dvl = findDiv (divs@divs1) sign
        (* sequence the divergence critic cannot apply *)
        val restOfDivs = LU.diff (LU.diff (divs@divs1,dvl),L.map (fn xs => (L.map (fn ((s,t),ty) => ((t,s),ty)) xs)) dvl)
        (* lemmas by divergence critic *)
        val dcl = L.filter (fn ((l,r),ty) => not(l=r)) (L.concat (L.map (fn l => divergenceCritic l) dvl))
        (* lemmas by new method *)
        val lem = L.filter (fn ((l,r),ty) => not(l=r)) (L.concat (L.map (fn l => newLemmaGeneralization l) divs ))
        val checkeqs = checkequal (LU.union (dcl@lem,nil))
        val _ = print "\n-------------Divergence series used in Divergence Critic---------------\n"
        val _ = if dvl = nil then print "\t[  ]\n\n"
                else L.app (fn x => print (Trs.prRules (MS.dropSortInMsRules x))) dvl
        val _ = print "---------------------The rest of divergence series-----------------------\n"
        val _ = if restOfDivs = nil then print "\t[  ]\n\n"
                else L.app (fn x => print (Trs.prRules (MS.dropSortInMsRules x))) restOfDivs
        val _ = print "Divergence critic\n"
        val _ = print (Trs.prEqs (MS.dropSortInMsRules dcl))
        val _ = print "\n"
        val _ = print "Lemma Generation based on Difference Match & Generalization\n"
        val _ = print (Trs.prEqs (MS.dropSortInMsRules lem))
    in
        checkeqs
    end


(* lemma generation based on random generation of rhs *)
fun postulateRand rs hs (sign,cfuns,dfuns) grter =
    let
        (* randomly generate lemmas for one sequence *)
        fun newLemGen1 [] = []
          | newLemGen1 ((l::ls)::lss) =
            case L.length ls of
                0 => nil
              | _ => Lemma.lemmaGen1Def (l,L.hd ls) (sign,dfuns,cfuns) grter (* randomly lemma generation *)

        (* randomly generate lemmas for all sequences *)
        fun LemGenRand [] = []
          | LemGenRand ls = case newLemGen1 ls of
                                [] => LemGenRand (L.tl ls)
                              | lemmas => lemmas@(LemGenRand (L.tl ls))
                                                     
        val hs1 = L.rev (decompose0 hs (sign,cfuns))
        val divs = L.filter (fn x => not(x=nil)) (extract hs1 nil (sign,cfuns,dfuns))
        (* sequence the divergence critic can apply *)
        val dvl = findDiv divs sign
        (* sequence the divergence critic cannot apply *)
        val restOfDivs = LU.diff (LU.diff (divs,dvl),L.map (fn xs => (L.map (fn ((s,t),ty) => ((t,s),ty)) xs)) dvl)
        val newlems = LemGenRand (dvl@restOfDivs)
    in
        newlems
    end

(* lemma generation based on random generation of rhs ~Debug Version~ *)
fun postulateRandPrint rs hs (sign,cfuns,dfuns) grter =
    let
        (* randomly generate lemmas for one sequence *)
        fun newLemGen1 [] = []
          | newLemGen1 ((l::ls)::lss) =
            case L.length ls of
                0 => nil
              | _ => Lemma.lemmaGen1PrintDef (l,L.hd ls) (sign,dfuns,cfuns) grter (* randomly lemma generation *)

        (* randomly generate lemmas for all sequences *)
        fun LemGenRand [] = []
          | LemGenRand ls = case newLemGen1 ls of
                                [] => LemGenRand (L.tl ls)
                              | lemmas => lemmas@(LemGenRand (L.tl ls))

        val hs1 = L.rev (decompose0 hs (sign,cfuns))
        val divs = L.filter (fn x => not(x=nil)) (extract hs1 nil (sign,cfuns,dfuns))
        (* sequence the divergence critic can apply *)
        val dvl = findDiv divs sign
        (* sequence the divergence critic cannot apply *)
        val restOfDivs = LU.diff (LU.diff (divs,dvl),L.map (fn xs => (L.map (fn ((s,t),ty) => ((t,s),ty)) xs)) dvl)
        val newlems = LemGenRand (dvl@restOfDivs)
    in
        newlems
    end

(* lemma generation based on random generation of rhs (depth input) *)
fun postulateRandDepth rs hs (sign,cfuns,dfuns) grter depth =
    let
        (* randomly generate lemmas for one sequence *)        
        fun newLemGen1 [] = []
          | newLemGen1 ((l::ls)::lss) =
            case L.length ls of
                0 => nil
              | _ => Lemma.lemmaGen1 (l,L.hd ls) (sign,dfuns,cfuns) grter depth (* ランダム補題生成 *)

        (* randomly generate lemmas for all sequences *)
        fun LemGenRand [] = []
          | LemGenRand ls = case newLemGen1 ls of
                                [] => LemGenRand (L.tl ls)
                              | lemmas => lemmas@(LemGenRand (L.tl ls))

        val hs1 = L.rev (decompose0 hs (sign,cfuns))
        val divs = L.filter (fn x => not(x=nil)) (extract hs1 nil (sign,cfuns,dfuns))
        (* sequence the divergence critic can apply *)
        val dvl = findDiv divs sign
        (* sequence the divergence critic cannot apply *)
        val restOfDivs = LU.diff (LU.diff (divs,dvl),L.map (fn xs => (L.map (fn ((s,t),ty) => ((t,s),ty)) xs)) dvl)
        val newlems = LemGenRand (dvl@restOfDivs)
    in
        newlems
    end

(* lemma generation based on random generation of rhs (depth input) ~Debug Version~ *)
fun postulateRandDepthPrint rs hs (sign,cfuns,dfuns) grter depth =
    let

        (* randomly generate lemmas for one sequence *)        
        fun newLemGen1 [] = []
          | newLemGen1 ((l::ls)::lss) =
            case L.length ls of
                0 => nil
              | _ => Lemma.lemmaGen1Print (l,L.hd ls) (sign,dfuns,cfuns) grter depth (* ランダム補題生成 *)

        (* randomly generate lemmas for all sequences *)
        fun LemGenRand [] = []
          | LemGenRand ls = case newLemGen1 ls of
                                [] => LemGenRand (L.tl ls)
                              | lemmas => lemmas@(LemGenRand (L.tl ls))

        val hs1 = L.rev (decompose0 hs (sign,cfuns))
        val divs = L.filter (fn x => not(x=nil)) (extract hs1 nil (sign,cfuns,dfuns))
        (* sequence the divergence critic can apply *)                            
        val dvl = findDiv divs sign
        (* sequence the divergence critic cannot apply *)                          
        val restOfDivs = LU.diff (LU.diff (divs,dvl),L.map (fn xs => (L.map (fn ((s,t),ty) => ((t,s),ty)) xs)) dvl)
        val newlems = LemGenRand (dvl@restOfDivs)
    in
        newlems
    end

(* induction step of lemma generation system *)
fun lemGenStep ((dfuns,cfuns,sign),rs,grter) (es,hs) =
    let
        val (es1,hs1) = expand ((dfuns,cfuns),rs,grter) (es,hs)
        val (es2,hs2) = simplify (rs,grter) (es1,hs1)
        val (es3,hs3) = decompose (sign,cfuns) (es2,hs2)
        val (es4,hs4) = delete (es3,hs3)
    in
        (es4,hs4)
    end

(* lemma generation system *)
fun lemGen (sign,rs,grter) es =
    let
        val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
        val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
        val (es',hs') = delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
        val _ = if null es' then raise Success else ()
        val max = 6
        fun lemGensub n (es0,hs0) =
            if n > max
            then
                let
                    val lemmas = postulate rs hs0 (sign,cfuns,dfuns)
                    val _ = if null lemmas then raise Stopped else ()
                in
                    lemmas
                end
            else
                let
                    val (es1,hs1) = lemGenStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
                in
                    if null es1
                    then raise Success
                    else lemGensub (n+1) (es1,hs1)
                end
    in
        lemGensub 1 (es',[])
        handle Success => []
             | Failure => []
             | Stopped => []
    end

(* lemma generation system ~Debug Version~ *)
fun lemGenPrint (sign,rs,grter) es =
    let
        val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
        val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
        val (es',hs') = delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
        val _ = if null es' then raise Success else ()
        val max = 6
        fun lemGensub n (es0,hs0) =
            if n > max
            then
                let
                    val lemmas = postulatePrint rs hs0 (sign,cfuns,dfuns) 
                    val _ = if null lemmas then raise Stopped else ()
                in
                    lemmas
                end
            else
                let
                    val (es1,hs1) = lemGenStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
                in
                    if null es1
                    then raise Success
                    else lemGensub (n+1) (es1,hs1)
                end
    in
        lemGensub 1 (es',[])
        handle Success => (print "Success\n\n"; [])
             | Failure => (print "Failed\n\n"; [])
             | Stopped => []
    end

(* randomly lemma generation system *)
fun randLemGenDef (sign,rs,grter) es =
    let
        val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
        val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
        val (es',hs') = delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
        val _ = if null es' then raise Success else ()
        val max = 6
        fun lemGensub n (es0,hs0) =
            if n > max
            then
                let
                    val lemmas = postulateRand rs hs0 (sign,cfuns,dfuns) grter
                    val _ = if null lemmas then raise Stopped else ()
                in
                    lemmas
                end
            else
                let
                    val (es1,hs1) = lemGenStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
                in
                    if null es1
                    then raise Success
                    else lemGensub (n+1) (es1,hs1)
                end
    in
        lemGensub 1 (es',[])
        handle Success => []
             | Failure => []
             | Stopped => []
    end
        
(* randomly lemma generation system ~Debug Version~*)
fun randLemGenDefPrint (sign,rs,grter) es =
    let
        val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
        val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
        val (es',hs') = delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
        val _ = if null es' then raise Success else ()
        val max = 6
        fun lemGensub n (es0,hs0) =
            if n > max
            then
                let
                    val lemmas = postulateRandPrint rs hs0 (sign,cfuns,dfuns) grter
                    val _ = if null lemmas then raise Stopped else ()
                in
                    lemmas
                end
            else
                let
                    val (es1,hs1) = lemGenStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
                in
                    if null es1
                    then raise Success
                    else lemGensub (n+1) (es1,hs1)
                end
    in
        lemGensub 1 (es',[])
        handle Success => []
             | Failure => []
             | Stopped => []
    end

(* randomly lemma generation system(depth input) *)
fun randLemGenDepth (sign,rs,grter) es depth =
    let
        val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
        val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
        val (es',hs') = delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
        val _ = if null es' then raise Success else ()
        val max = 6
        fun lemGensub n (es0,hs0) =
            if n > max
            then
                let
                    val lemmas = postulateRandDepth rs hs0 (sign,cfuns,dfuns) grter depth
                    val _ = if null lemmas then raise Stopped else ()
                in
                    lemmas
                end
            else
                let
                    val (es1,hs1) = lemGenStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
                in
                    if null es1
                    then raise Success
                    else lemGensub (n+1) (es1,hs1)
                end
    in
        lemGensub 1 (es',[])
        handle Success => []
             | Failure => []
             | Stopped => []
    end
        
(* randmly lemma generation system (depth input) ~Debug Version~*)
fun randLemGenDepthPrint (sign,rs,grter) es depth =
    let
        val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
        val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
        val (es',hs') = delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
        val _ = if null es' then raise Success else ()
        val max = 6
        fun lemGensub n (es0,hs0) =
            if n > max
            then
                let
                    val lemmas = postulateRandDepthPrint rs hs0 (sign,cfuns,dfuns) grter depth
                    val _ = if null lemmas then raise Stopped else ()
                in
                    lemmas
                end
            else
                let
                    val (es1,hs1) = lemGenStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
                in
                    if null es1
                    then raise Success
                    else lemGensub (n+1) (es1,hs1)
                end
    in
        lemGensub 1 (es',[])
        handle Success => []
             | Failure => []
             | Stopped => []
    end


(* -----------experimental---------------- *)
fun postulateDc rs hs (sign,cfuns,dfuns) =
    let
        (* we apply the divergence critic *)
        fun divergenceCritic ((l,ty)::ls) =
            case L.length ls of
                0 => nil
              | _ => DcMs.dcMs ((l,ty),(L.hd ls)) (sign,cfuns)

        val hs1 = L.rev (decompose0 hs (sign,cfuns))
        val divs = L.filter (fn x => not(x=nil)) (extract hs1 nil (sign,cfuns,dfuns))
        (* the set of hypotheses other than the divergence sequence discovered by extract *)                            
        val rest1 = LU.diff (hs1,(L.concat divs))
        (* sequence the divergence critic can apply *)           
        val dvl = findDiv divs sign
        (* divergence critic *)
        val dcl = L.filter (fn ((l,r),ty) => not(l=r)) (L.concat (L.map (fn l => divergenceCritic l) dvl))
        val checkeqs = checkequal dcl
    in
        checkeqs
    end

(* divergence critic *)
fun DivCritic (sign,rs,grter) es =
    let
        val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
        val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
        val (es',hs') = delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
        val _ = if null es' then raise Success else ()
        val max = 6
        fun lemGensub n (es0,hs0) =
            if n > max
            then
                let
                    val lemmas = postulateDc rs hs0 (sign,cfuns,dfuns)
                    val _ = if null lemmas then raise Stopped else ()
                in
                    lemmas
                end
            else
                let
                    val (es1,hs1) = lemGenStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
                in
                    if null es1
                    then raise Success
                    else lemGensub (n+1) (es1,hs1)
                end
    in
        lemGensub 1 (es',[])
        handle Success => []
             | Failure => []
             | Stopped => []
    end

(* lemma generation method based on generalization and difference matching *)
fun postulateDm rs hs (sign,cfuns,dfuns) =
    let
        (* 差分照合と一般化に基づく補題生成法の適用 *)
        (* we apply lemma generation method based on generalization and difference matching *)
        fun newLemmaGeneralization (l::ls) =
            case L.length ls of
                0 => nil
              | _ => Lemma.lemmagen (l,L.hd ls) (sign,cfuns)

        val hs1 = L.rev (decompose0 hs (sign,cfuns))
        val divs = L.filter (fn x => not(x=nil)) (extract hs1 nil (sign,cfuns,dfuns))
        (* the set of hypotheses other than the divergence sequence discovered by extract *)
        val rest1 = LU.diff (hs1,(L.concat divs))
        (* sequence the divergence critic can apply *)
        val dvl = findDiv divs sign
        (* lemma generation method based on generalization and difference matching *)                          
        val lem = L.filter (fn ((l,r),ty) => not(l=r)) (L.concat (L.map (fn l => newLemmaGeneralization l) divs))
        val checkeqs = checkequal lem
    in
        checkeqs
    end
        
fun DmNewLem (sign,rs,grter) es =
    let
        val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
        val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
        val (es',hs') = delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
        val _ = if null es' then raise Success else ()
        val max = 6
        fun lemGensub n (es0,hs0) =
            if n > max
            then
                let
                    val lemmas = postulateDm rs hs0 (sign,cfuns,dfuns)
                    val _ = if null lemmas then raise Stopped else ()
                in
                    lemmas
                end
            else
                let
                    val (es1,hs1) = lemGenStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
                in
                    if null es1
                    then raise Success
                    else lemGensub (n+1) (es1,hs1)
                end
    in
        lemGensub 1 (es',[])
        handle Success => []
             | Failure => []
             | Stopped => []
    end
        
end (* of local *)
    
end (* of struct *)
