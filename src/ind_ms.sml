(* file: ind_ms.sml *)
(* Inductive theorem prover with disproof in many-sorted TRS *)
(* author: Hiroto Kato *)

signature INDMS =
sig 
    val expd: ManySorted.ms_rules -> ManySorted.ms_rule -> Term.context * Term.term -> ManySorted.ms_rules
    val expand: (Term.fun_key list * Term.fun_key list) * ManySorted.ms_rules * (Trs.rule -> bool) -> (ManySorted.ms_eqs * ManySorted.ms_rules) -> ManySorted.ms_eqs * ManySorted.ms_rules
    val simplify: ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs * ManySorted.ms_rules -> ManySorted.ms_eqs * ManySorted.ms_rules
    val delete: ManySorted.ms_eqs * ManySorted.ms_rules -> ManySorted.ms_eqs * ManySorted.ms_rules
    val decompose: ManySorted.ms_sign * Term.fun_key list -> ManySorted.ms_eqs *ManySorted.ms_rules -> ManySorted.ms_eqs * ManySorted.ms_rules
    val disproof: Term.fun_key list -> ManySorted.ms_eqs * ManySorted.ms_rules -> bool
    val indStep: (Term.fun_key list * Term.fun_key list * ManySorted.ms_sign) * ManySorted.ms_rules * (Trs.rule -> bool) -> (ManySorted.ms_eqs * ManySorted.ms_rules) -> ManySorted.ms_eqs * ManySorted.ms_rules
    val indStepPrint: (Term.fun_key list * Term.fun_key list * ManySorted.ms_sign) * ManySorted.ms_rules * (Trs.rule -> bool) -> (ManySorted.ms_eqs * ManySorted.ms_rules) -> ManySorted.ms_eqs * ManySorted.ms_rules
    val ind: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> int -> string (*bool*)
    val indPrint: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) -> ManySorted.ms_eqs -> int -> string (*bool*)
end 

structure IndMs:INDMS = 
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
exception Disproof

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
      fun sizePos t = L.length (T.pos t)
      fun size ((s,t),ty) = L.length (T.pos s) + L.length (T.pos t)
      fun check ((s,t),ty) = if grter (s,t) then SOME ((s,t),ty)
			     else if grter (t,s) then SOME ((t,s),ty)
			     else case (T.isDfunInRoot dfuns s,T.isDfunInRoot dfuns t) of
				      (true,false) => SOME ((s,t),ty)
				    | (false,true) => SOME ((t,s),ty)
				    | (_,_) => if sizePos s > sizePos t then SOME ((s,t),ty)
					       else if sizePos s < sizePos t then SOME ((t,s),ty)
					       else SOME ((s,t),ty)
							 
      fun select nil = NONE
	| select xs = case (L.mapPartial (fn x => check x) xs) of
			  nil => NONE
			| rules => SOME rules

      fun removeEq rs es = LU.diff (es,rs@(L.map (fn ((s,t),ty) => ((t,s),ty)) rs))
	
      fun selectAndExpand es0 =
	case select es0 of(*SOME (L.concat (L.map (fn ((s,t),ty) => expd rs ((s,t),ty) (valOf (T.findBasicSubtermLiOc (dfuns,cfuns) s))) rules), rules)*)
	    SOME rules => (case (L.concat (L.map (fn ((s,t),ty) => case T.findBasicSubtermLiOc (dfuns,cfuns) s of
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
      fun mainDecompose ((t,u),ty) = if T.isFun t then
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
				     else
					 [((t,u),ty)]
  in
      (L.concat (L.map (fn ((x,y),ty) => mainDecompose ((x,y),ty)) es),hs)
  end

fun disproof cfuns (es,hs) =
  let
      fun disproof1 (s,T.Var x) = not(LU.member x (T.vars s))
	| disproof1 (T.Var x,s) = not(LU.member x (T.vars s))
	| disproof1 (_,_) = false
				
      fun disproof2 (T.Fun (f,ts),T.Var x) cfuns = if LU.member f cfuns then true
					       else false
	| disproof2 (T.Var x,T.Fun (f,ts)) cfuns = if LU.member f cfuns then true
					       else false
	| disproof2 (_,_) cfuns = false
				      
      fun disproof3 (T.Fun (f,ts),T.Fun (g,us)) cfuns = LU.member f cfuns andalso LU.member g cfuns andalso not(f=g)
	| disproof3 (_,_) cfuns = false
				      
  in
      L.exists (fn ((l,r),ty) => if T.isFun l andalso T.isFun r then disproof3 (l,r) cfuns
			      else disproof1 (l,r) orelse disproof2 (l,r) cfuns) es
  end

(* 反証機能付き書き換え帰納法の帰納ステップ *)
fun indStep ((dfuns,cfuns,sign),rs,grter) (es,hs) =
  let
      val (es1,hs1) = expand ((dfuns,cfuns),rs,grter) (es,hs)
      val (es2,hs2) = simplify (rs,grter) (es1,hs1)
      val (es3,hs3) = decompose (sign,cfuns) (es2,hs2)
      val (es4,hs4) = simplify (rs,grter) (es3,hs3)
      val (es5,hs5) = delete (es4,hs4)
      val nonTheorem = disproof cfuns (es5,hs5)
  in
      if nonTheorem then raise Disproof else (es5,hs5)
  end

(* 反証機能付き書き換え帰納法の帰納ステップ ~Debug Version~*)
fun indStepPrint ((dfuns,cfuns,sign),rs,grter) (es,hs) =
  let
      val (es1,hs1) = expand ((dfuns,cfuns),rs,grter) (es,hs)
      val e = Comp.pr "expand\n" (MS.dropSortInMsEqs es1,MS.dropSortInMsRules hs1)
      val (es2,hs2) = simplify (rs,grter) (es1,hs1)
      val s = Comp.pr "simplify\n" (MS.dropSortInMsEqs es2,MS.dropSortInMsRules hs2)
      val (es3,hs3) = decompose (sign,cfuns) (es2,hs2)
      val d = Comp.pr "decompose\n" (MS.dropSortInMsEqs es3,MS.dropSortInMsRules hs3)
      val (es4,hs4) = simplify (rs,grter) (es3,hs3)
      val s = Comp.pr "simplify\n" (MS.dropSortInMsEqs es4,MS.dropSortInMsRules hs4)
      val (es5,hs5) = delete (es4,hs4)
      val del = Comp.pr "delete\n" (MS.dropSortInMsEqs es5,MS.dropSortInMsRules hs5)
      val nonTheorem = disproof cfuns (es5,hs5)
  in
      if nonTheorem then raise Disproof else (es5,hs5)
  end

(* 反証機能付き書き換え帰納法 *)
fun ind (sign,rs,grter) es max =
  let
      val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
      val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
      (* 補題を追加したとき，以下の処理を飛ばす *)
      val (es',hs') = if L.length es = 1 then delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
		      else (es,[])
			       
      val _ = if null es' then raise Success
	      else (if disproof cfuns (es',hs') then raise Disproof else ())
		       
      fun indsub n (es0,hs0) =
	if n > max
	then
	    raise Stopped
	else
	    let
		val (es1,hs1) = indStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
	    in
		if null es1
		then raise Success
		else indsub (n+1) (es1,hs1)
	    end
  in
      indsub 1 (es',[])
      handle Success => ((*print "Success\n";*) "Success")
	   | Failure => ((*print "Failure\n";*) "Failure")
	   | Stopped => ((*print "Stopped\n\n";*) "Stopped")
	   | Disproof => ((*print "Conjectures are non-Inductive Theorems\n";*) "Disproof")
  end handle Success => "Success"
	   | Disproof => "Disproof"

(* 反証機能付き書き換え帰納法 ~Debug Version~ *)
fun indPrint (sign,rs,grter) es max =
  let
      val dfuns = LU.union ((L.mapPartial (fn ((l,r),ty) => Term.dfun l) rs),[])
      val cfuns = LU.diff (L.concat (L.map (fn ((l,r),ty) => LU.union ((T.funs l), (T.funs r))) rs),dfuns)
      (*val _ = print "We asuume that R is a left-linear quasi-reducible CS.\n"
      val _ = print "Check whether R is oriented w.r.t. given ordering...\n"
      (* Rが擬簡約かどうか *)
      val _ = if (L.all (fn ((l,r),ty) => ?) rs) 
	      then print "OK\n"
	      else (print "Failed\n"; raise Failure)*)
      (* 補題を追加したとき，以下の処理を飛ばす *)
      val (es',hs') = if L.length es = 1 then delete(decompose (sign,cfuns) (simplify (rs,grter) (es,[])))
		      else (es,[])
      val _ = if null es' then raise Success
	      else (if disproof cfuns (es',hs') then raise Disproof else ())
		       
      fun indsub n (es0,hs0) =
	  if n > max
	  then
	      raise Stopped
	  else
	      let
		  val _ = print ("[Step" ^ (Int.toString n) ^ "]\n")
		  val (es1,hs1) = indStep ((dfuns,cfuns,sign),rs,grter) (es0,hs0)
	      in
		  if null es1
		  then raise Success
		  else indsub (n+1) (es1,hs1)
	      end
  in
      indsub 1 (es',[])
      handle Success => (print "Success\n"; "Success"(*true*))
	   | Failure => (print "Failure\n"; "Failure"(*false*))
	   | Stopped => ((*print "Stopped\n\n";*) "Stopped"(*false*))
	   | Disproof => (print "Conjectures are non-Inductive Theorems\n"; "Disproof"(*false*))
  end handle Success => (print "Success\n"; "Success"(*true*))
			    
end (* of local *)

end (* of struct *)
