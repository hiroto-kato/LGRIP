(* file: dm_ms.sml *)
(* description: ManySorted Difference Matching *)
(* author: Hiroto Kato *)

signature DM_MS =
sig
    val wavehole: Term.context * Term.context * Term.term -> Term.term
    val skel: Term.context * Term.context * Term.term -> Term.term
    val erase: Term.context * Term.context * Term.term -> Term.term
    val toSigma: Term.context * Term.context * Term.term * Subst.subst -> Subst.subst
    val delSigma: Term.context * Term.context * Term.term * Subst.subst -> Term.context * Term.context * Term.term
    val checkDm: Term.term * Term.term -> Term.context * Term.context * Term.term * Subst.subst -> bool
    val unionCont: Subst.dmsubset * Subst.dmsubset -> Term.term -> Subst.dmsubset
    val msDifMatch: ManySorted.ms_sign -> ManySorted.ms_term * ManySorted.ms_term -> Subst.dmsubset
    val MaxDm: Subst.dmset -> Subst.dmset -> Subst.dmset
    val deleteNoDm: Subst.dmset -> Subst.dmset
    val isDif: ManySorted.ms_sign -> ManySorted.ms_rule -> ManySorted.ms_rules -> (Subst.dmset * Subst.dmset)
    val renameDm: Subst.dmset * Subst.dmset -> Subst.dmset * Subst.dmset

end

structure Dm_ms: DM_MS =
struct

local 
    structure L = List
    structure LU = ListUtil
    structure AL = AssocList
    structure T = Term
    structure LP = ListPair
    structure MS = ManySorted
in

(* 多ソートの差分照合 *)
fun wavehole (c1,c2,r) = r
fun skel (c1,c2,r) = c1 r
fun erase (c1,c2,r) = c1 (c2 r)
fun toSigma (c1,c2,r,sigma) = sigma
fun delSigma (c1,c2,r,sigma) = (c1,c2,r)
fun checkDm (s,t) (r as (c1,c2,r1,sigma)) = ((erase (delSigma r) = t) andalso (skel (delSigma r) = Subst.apply sigma s))

val term = T.fromString "?hole" (* hole *)
val hole = (T.makeContext term nil, T.makeContext term nil, term)

(* (context,context,term,sigma)のunion (_,nil,sigma)の時だけ順番を換えないようにする *)	       
fun unionCont ([],ys) term = ys
  | unionCont (((c1,c2,t,sigma)::xs),ys) term =
    let
	fun memberCont ((c1,c2,t,sigma),ys) t1 = List.exists (fn (c1',c2',t',sigma') => (c1 t1, c2 t1, t) = (c1' t1, c2' t1, t')) ys
	fun addCont ((c1,c2,t,sigma), ys) t1 = if memberCont ((c1,c2,t,sigma), ys) t1 then ys else L.rev ([(c1,c2,t,sigma)]@ys)
    in
	
	if memberCont ((c1,c2,t,sigma),ys) term  then unionCont (xs,ys) term
	else unionCont (xs, addCont ((c1,c2,t,sigma), ys) term) term
    end

fun msDifMatch sign ((t1,ty1),(t2,ty2)) =
  let
      val msVars = MS.sortAssignInMsTerms sign [(t1,ty1),(t2,ty2)]
      fun unionSigma dmi =
	let
	    val usigma = LU.union (L.concat (L.map (fn r => toSigma r) dmi),[])
	    val usigma1 = L.filter (fn (s,t) => not (L.exists (fn (x,y) => s=x) (LU.diff (usigma,[(s,t)])))) usigma
	in
	    usigma1
	end
	    
      fun dm (s as T.Var ss, t as T.Var ts) =
	let
	    val dm1 = [(T.makeContext s nil, T.makeContext t nil, t, [(ss,t)])]
	    val varOfs = Var.fromString (Term.toString s)
	    val varOft = Var.fromString (Term.toString t)
	    val dm0 = if (AL.find varOfs msVars = AL.find varOft msVars) then L.filter (fn r => checkDm (s,t) r) dm1
		      else nil
			       
	    (* デバック用 *)
	    (*val _ = print "dm(if s=var,t=var) \n"
	    val _ = Subst.dmToString1 dm0*)
	in
	    if (AL.find varOfs msVars = AL.find varOft msVars) then L.filter (fn r => checkDm (s,t) r) dm1
	    else nil
	end

	| dm (s as T.Var ss, t as T.Fun (f,ts)) =
	  let
	      val dmi = L.concat (L.map (fn ti => dm (s,ti)) ts)
	      val dm1 = L.map (fn (c1,c2,r,sigma) =>
				  (T.makeContext t ((T.termMatchPosition t ((T.makeContext t ((T.termMatchPosition t r))) r))), T.makeContext t ((T.termMatchPosition t r)), r, sigma) ) dmi

	      (* デバック用 *)
	      (*val _ = print "dm(if s=variable,t=fun) \n"
	      val _ = Subst.dmToString1 dm1*)
	  in
	      L.filter (fn r => checkDm (s,t) r) dm1
	  end
	| dm (s as T.Fun (g,ss), t as T.Fun (f,ts)) =
	  let
	      (* f(r1,...rn)のlistを作成 (保留している文脈リストにするところ) *)
	      fun dmfun (xs::ls) nil = dmfun ls (L.map (fn (c1,c2,r,sigma) => (f,[(c1 (c2 r))])) xs)
		| dmfun nil fl = fl
		| dmfun (xs::nil) fl = LP.map (fn ((c1,c2,r,sigma),(fx,ys)) => (fx,ys@[(c1 (c2 r))])) (xs,fl)
		| dmfun (xs::ls) fl = dmfun ls (LP.map (fn ((c1,c2,r,sigma),(fx,ys)) => (fx,ys@[(c1 (c2 r))])) (xs,fl))
	      (* (nil,nil,r) or (context,context,r) *)
	      fun dmx nil func = nil
		| dmx ((c1,c2,r,sigma)::dms) func =
		  if r = (c2 r) then ([(T.makeContext s nil, T.makeContext t nil, func,sigma)])@(dmx dms func)
		  else ([(T.makeContext func ((T.termMatchPosition func (c2 r))), c2, r,sigma)] @ (dmx dms func))
			   
	  in
	      if f=g then
		  if s=t then
		      let
			  (* dm(s,t) = {<s,fi>} *)
			  val dm0 = L.filter (fn r => checkDm (s,t) r) [(T.makeContext s nil, T.makeContext t nil, s, nil)]
			  (* デバッグ用 *)
			  (*val _ = print "dm(if s,t=f(si) and s=t) \n"
			  val _ = Subst.dmToString1 dm0*)
		      in
			  dm0
		      end
		  else
		      let
			  (* dm(s,t) = {<f(r1...rn),sigma)>}U{<f(t1..ri..tn),sigma>} *)
			  val dmi = L.concat (L.map (fn ti => dm (s,ti)) ts) (* -> a' list list *)
			  val dm1 = L.map (fn (c1,c2,r,sigma) => (T.makeContext t ((T.termMatchPosition t ((T.makeContext t (T.termMatchPosition t r)) r))), T.makeContext t ((T.termMatchPosition t r)), r, sigma) ) dmi
					  
			  (* dm(si,ti) < type is a' list list>*)
			  val dmix2 = LP.map (fn (si,ti) => unionCont (dm (si,ti),[]) term) (ss,ts)
			  val dmi2 = L.concat dmix2
			  val dmi2Unionsigma = unionSigma dmi2 (* sigma = Ui(sigma_i) *)
			  val dmifun = L.map (fn x => T.Fun x) (dmfun dmix2 nil)
			  val dm2 = L.map (fn (c1,c2,r,sigma) => (c1,c2,r,dmi2Unionsigma)) (L.concat (L.map (fn fx => dmx dmi2 fx) dmifun))
			  val dm12 = L.filter (fn r => checkDm (s,t) r) (unionCont (dm1@dm2,[]) term)
			  (* デバッグ用 *)
			  (*val _ = print ((toString dmi2Unionsigma) ^ "\n")
			  val _ = List.map (fn x => print ((T.toString x) ^ "\n")) dmifun
			  val _ = print "\n"
			  val _ = List.map (fn (c1,c2,r) => print ((" < " ^ (Term.toString (c1 term)) ^ "," ^ (Term.toString (c2 term)) ^ "," ^ (Term.toString r)) ^ " >,")) (L.map (fn x => delSigma x) dmi2)
			  val _ = print "\n"*)
			  (*val _ = Subst.dmToString1 dm2*)
			  (*val _ = print "dm2(if s=f(si),t=f(ti)) \n"
			  val _ = Subst.dmToString1 dm12*)
		      in
			  dm12
		      end
	      else
		  let
		      (* dm(s,t) = {<f(t1..ri..tn),sigma>} *)
		      val dmi = L.concat (L.map (fn ti => dm (s,ti)) ts)
		      val dm1 = L.map (fn (c1,c2,r,sigma) => (T.makeContext t ((T.termMatchPosition t ((T.makeContext t (T.termMatchPosition t r)) r))), T.makeContext t ((T.termMatchPosition t r)), r, sigma) ) dmi
		      val dm0 = L.filter (fn r => checkDm (s,t) r) dm1
		      (* デバッグ用 *)
		      (*val _ = print "dm1(if s=g(sm),t=f(ti)) \n"
		      val _ = Subst.dmToString1 dm0*)
		  in
		      dm0
		  end
	  end
	      
	| dm (_,_) = []
			 
      val differenceMatching = L.filter (fn r => checkDm (t1,t2) r) (dm (t1,t2))
      (* デバッグ用 *)
      (*val _ = Subst.dmToString (L.map (fn x => delSigma x) differenceMatching)*)
  in
      if t1=t2 then [(T.makeContext t2 nil, T.makeContext t2 nil, t2, [])]
      else differenceMatching
  end 

(* maximal difference matching *)
fun MaxDm (x::nil) nil = [x]
  | MaxDm nil ts = ts
  | MaxDm (x::xs) nil = MaxDm xs [x]
  | MaxDm ((c1,c2,r)::xs) (ts as ((c1',c2',r')::ys)) = 
    let 
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
		
    in 
	if size (erase (c1,c2,r), (c2 r)) = size (erase (c1',c2',r'), (c2' r')) then MaxDm xs (unionC (ts@[(c1,c2,r)],nil) term)
	else (if (size (erase (c1,c2,r) ,(c2 r))) < (size (erase (c1',c2',r'), (c2' r'))) then MaxDm xs [(c1,c2,r)]
	      else MaxDm xs ts)
    end

(* differenceMatchではないものをdelete*)
fun deleteNoDm ts =
    let
      val d = case (L.filter (fn t1 => not(erase t1 = wavehole t1)) ts) of 
		    nil => nil (*[hole] *)
		  | x => x
    in
	d
    end

(* (l0,r0)と差分があるようなルールを１つ見つける *)
fun isDif sign ((l0,r0),ty0) nil = (nil,nil)
  | isDif sign ((l0,r0),ty0) (((l1,r1),ty1)::rest) = 
    let 
	val dmleft1 = deleteNoDm (L.map (fn x => delSigma x) (msDifMatch sign ((l0,ty0),(l1,ty1)))) handle NotWellSorted => nil
	val dml1 = deleteNoDm (MaxDm dmleft1 nil)  (* maximal difference matching of left hand *)  
	val dmright1 = deleteNoDm (L.map (fn x => delSigma x) (msDifMatch sign ((r0,ty0),(r1,ty1)))) handle NotWellSorted => nil
	val dmr1 = deleteNoDm (MaxDm dmright1 nil)  (* maximal difference matching of right hand *)
    in
	case (dml1,dmr1) of
	    (nil,_) => isDif sign ((l0,r0),ty0) rest 
	  | (ls,rs) => (ls,rs)
    end

(* <D,C,t> rename*)
fun renameDm ((cl,cl',l)::nil,(cr,cr',r)::nil) =
  let
      val hole = T.fromString "hole";
      val vl = LU.union (T.vars (cl (cl' l)),T.vars (cr (cr' r)))
      val max = L.foldr (fn ((x,i),n) => Int.max (i,n)) 0 vl
      fun rename1 (T.Var (x,i)) = T.Var (x,max+i+1)
	| rename1 (T.Fun (f,ts)) = T.Fun (f, (L.map rename1 ts))

      val cl1 = rename1 (cl hole) 
      val cl1' = rename1 (cl' hole)
      val l1 = rename1 l
      val cl2 = T.makeContext cl1 (T.termMatchPosition cl1 hole)
      val cl2' = T.makeContext cl1' (T.termMatchPosition cl1' hole)
		       
      val cr1 = rename1 (cr hole)
      val cr1' = rename1 (cr' hole)
      val r1 = rename1 r
      val cr2 = T.makeContext cr1 (T.termMatchPosition cr1 hole)
      val cr2' = T.makeContext cr1' (T.termMatchPosition cr1' hole)
			       
  in
      ([(cl2,cl2',l1)],[(cr2,cr2',r1)])
  end
  | renameDm (_,_) = (nil,nil)
			 
end (* of local *)
    
end

