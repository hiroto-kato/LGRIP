(* file: subst.sml *)
(* description: substutition *)
(* author: Hiroto Kato *)

signature SUBST = 
sig 
    type subst
    type dmset
    type dmsubset
    val apply: subst -> Term.term -> Term.term
    val dom: subst -> Var.key list
    val match: Term.term -> Term.term -> subst option
    val toString: subst -> string
    val compose: subst -> subst -> subst
    val unify: Term.term * Term.term -> subst option
    val unionCont: dmsubset * dmsubset -> Term.term -> dmsubset
    val difMatch: Term.term * Term.term -> dmsubset
    val dmToString: dmset -> unit
    val dmToString1: dmsubset -> unit
    val matchVar: Term.term -> Term.term -> subst option
    val MaxDm: dmset -> dmset -> dmset
    val deleteNoDm: dmset -> dmset
    val isDif: Term.term * Term.term -> (Term.term * Term.term) list -> (dmset * dmset) 
end

structure Subst: SUBST =
struct 

local 
    structure L = List
    structure LU = ListUtil
    structure AL = AssocList
    structure T = Term
    structure LP = ListPair
in

type subst = (Var.key * Term.term) list
type dmset = (Term.context * Term.context * Term.term) list
type dmsubset = (Term.context * Term.context * Term.term * subst) list

fun apply sigma (T.Var x) = (case AL.find x sigma 
    	  	       	    	  of NONE => T.Var x
				  | _ => valOf (AL.find x sigma)
				  )
  | apply sigma (T.Fun (f,ts)) = T.Fun (f, L.map (apply sigma) ts) 

(* domain *)
fun dom nil = nil
    | dom sigma = case L.hd sigma
    	      	  of (k,T.Var v) => if k=v then dom (L.tl sigma)
		   	       	    else k::(dom (L.tl sigma))
		  | (k,T.Fun v) => k::(dom (L.tl sigma))

(* matching *)
fun match pattern term =
    let
	fun decompose ts us = LP.map (fn (x,y) => (x,y)) (ts,us)
	fun unionPair [] us = us
	    | unionPair ts [] = ts
	    | unionPair ((k,v)::ts) ((a,b)::us) = if k=a andalso v=b then unionPair ts ((a,b)::us)
	      			    		  else unionPair ts ((k,v)::(a,b)::us)
	fun main [] sigma = SOME sigma
	    | main ((T.Fun (f,ts),T.Fun (g,us))::rest) sigma = if f=g then main (unionPair (decompose ts us) rest) sigma 
	       	       		    		   	   else NONE
	    | main ((T.Fun _, T.Var _)::_) _ = NONE
 	    | main ((T.Var x, t0)::rest) sigma = case AL.find x sigma
	      	   	       	  	     	 of NONE => main rest (valOf (AL.add (x,t0) sigma))
						 | SOME t1 => if t1=t0 then main rest sigma else NONE
    in main [(pattern,term)] []
    end

(* matching for variable *)
fun matchVar pattern term =
  let
      fun makePair (h0::t0) (h1::t1) = (h0,h1)::(makePair t0 t1)
	| makePair nil nil = nil
      fun main nil sigma = SOME sigma
	| main ((T.Var x, T.Fun(f,ts))::rest) sigma = NONE
	| main ((T.Var x, t0)::rest) sigma =
	  if (AL.find x sigma) = NONE
	  then main rest ((x,t0)::sigma)
	  else if (AL.find x sigma) = (SOME t0) then main rest sigma
	  else NONE
	| main ((T.Fun (f,ts),T.Fun (g,us))::rest) sigma =
	  if f=g then main ((LP.map (fn (x,y) => (x,y)) (ts,us))@rest) sigma else NONE
	| main ((T.Fun _, T.Var _)::_) _  = NONE
  in main [(pattern,term)] nil
  end	

(* print subst *)
fun toString nil = "{}"
    | toString ((x,t)::nil) = "{?" ^ (Var.toString x) ^ (" := ") ^ (Term.toString t) ^ "}"
    | toString ((x,t)::rest) = "{?" ^ (Var.toString x) ^ (" := ") ^ (Term.toString t) ^ "," ^ (toStringTerm rest)
and toStringTerm nil = "{}"
    | toStringTerm ((x,t)::nil) = "?" ^ (Var.toString x) ^ (" := ") ^ (Term.toString t) ^ "}"
    | toStringTerm ((x,t)::rest) = "?" ^ (Var.toString x) ^ (" := ") ^ (Term.toString t) ^ "," ^ (toStringTerm rest)

(* composition of substitutions: rho o sigma *)
fun compose sigma rho = (L.map (fn (x,y) => (x, (apply rho y))) sigma) @ rho

(* 単一化 *)
fun unify (term1,term2) = 
    let fun main [] sigma = SOME sigma
	  | main ((T.Var x, t)::rest) sigma = (case (T.Var x)=t 
					       of true => main rest sigma
						| false => (if (L.exists (fn y => y=x) (T.vars t)) then NONE 
							    else main (L.map (fn (a,y) => (apply [(x,t)] a,apply [(x,t)] y)) rest) (compose sigma [(x,t)])))
	  
	  | main ((T.Fun (f,ts),T.Fun (g,us))::rest) sigma = if f=g then main ((LP.map (fn (x,y) => (x,y)) (ts,us))@rest) sigma
							     else NONE
	  
	  | main ((t,T.Var x)::rest) sigma = main ((T.Var x, t)::rest) sigma
    in main [(term1,term2)] []
    end
	
(*以下差分照合*)
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


fun dmToString dm = 
  let
      val t = T.fromString "?hole"
      fun wavehole (c1,c2,r) = r
      fun skel (c1,c2,r) = c1 r
      fun erase (c1,c2,r) = c1 (c2 r)
      fun delsigma (c1,c2,r,sigma) = (c1,c2,r)      
      fun toSigma (c1,c2,r,sigma) = sigma
      fun dif (c1,c2,r) = c2 t
      fun dif1 (c1,c2,r) = c1 t

      fun rules nil = " < " ^ (T.toString t) ^ " / " ^ (T.toString t) ^ " / " ^ (T.toString t) ^ " > "
	| rules (r::nil) = " < " ^ (T.toString (dif1 r)) ^ " / " ^ (T.toString (dif r)) ^ " / " ^ (T.toString (wavehole r)) ^ " > "
	| rules (r::rs) = " < " ^ (T.toString (dif1 r)) ^ " / " ^ (T.toString (dif r)) ^ " / " ^ (T.toString (wavehole r)) ^ " >  / " ^ (rules rs)

      val _ = print "\t[ "
      val _ = print (rules dm)
      val _ = print " ]\n"
  in
      print ""
  end

(* 代入もあるversion*)
fun dmToString1 dm = 
  let
      val t = T.fromString "?hole"
      fun wavehole (c1,c2,r,sigma) = r
      fun skel (c1,c2,r,sigma) = c1 t
      fun erase (c1,c2,r,sigma) = c1 (c2 r)
      fun dif (c1,c2,r,sigma) = c2 t
      fun toSigma (c1,c2,r,sigma) = sigma
			     
      fun rules nil = " < " ^ (T.toString t) ^ " / " ^ (T.toString t) ^ " / " ^ (T.toString t) ^  " > "
	| rules (r::nil) = " < " ^ (T.toString (skel r)) ^ " / " ^ (T.toString (dif r)) ^ " / " ^ (T.toString (wavehole r)) ^ " / " ^ (toString (toSigma r)) ^ " > "
	| rules (r::rs) = " < " ^ (T.toString (skel r)) ^ " / " ^ (T.toString (dif r)) ^ " / " ^ (T.toString (wavehole r)) ^ " / " ^ (toString (toSigma r)) ^ " >  / " ^ (rules rs)

      val _ = print "\t[ "
      val _ = print (rules dm)
      val _ = print " ]\n"
  in
      print ""
  end

(* difference matching *)	
fun difMatch (t1,t2) =
  let
      val term = T.fromString "?hole" (* デバック用 *)
      fun wavehole (c1,c2,r,sigma) = r
      fun skel (c1,c2,r,sigma) = c1 r
      fun erase (c1,c2,r,sigma) = c1 (c2 r)
      fun toSigma (c1,c2,r,sigma) = sigma
      fun checkDm (s,t) (r as (c1,c2,r1,sigma)) =
	let
	    (*val _ = print (toString sigma) 
	    val _ = print "\n\n"
	    val _ = print ((T.toString (erase r)) ^ "\t" ^ (T.toString t) ^ "\n")
	    val _ = print ((T.toString (skel r)) ^ "\t" ^ (T.toString (apply sigma s)) ^ "\n")
	    val _ = print "\n"*)
	in
	    ((erase r = t) andalso (skel r = apply sigma s))
	end
	    
      fun unionSigma dmi =
	let
	    val usigma = LU.union (L.concat (L.map (fn r => toSigma r) dmi),[])
	    val usigma1 = L.filter (fn (s,t) => not (L.exists (fn (x,y) => s=x) (LU.diff (usigma,[(s,t)])))) usigma
	in
	    usigma1
	end
	    
      fun delsigma (c1,c2,r,sigma) = (c1,c2,r)

      (* 差分照合のアルゴリズム *)
      fun dm (s as T.Var ss, t as T.Var ts) =
	let
	    val dm1 = [(T.makeContext s nil, T.makeContext t nil, t, [(ss,t)])]
	    (* デバック用 *)
	    (*val _ = print "dm(if s=variable,t=variable) \n"
	    val _ = dmToString1 (L.filter (fn r => checkDm (s,t) r) dm1)
	    val _ = dmToString (L.map (fn x => delsigma x) (L.filter (fn r => checkDm (s,t) r) dm1))*)
	in
	    L.filter (fn r => checkDm (s,t) r) dm1
	end
	    
	| dm (s as T.Var ss, t as T.Fun (f,ts)) =
	  let
	      val dmi = L.concat (L.map (fn ti => dm (s,ti)) ts)
	      (* termMatchposが複数ある時に間違うので元のtermに合うやつを選ぶ *)
	      val dm1 = L.map (fn (c1,c2,r,sigma) =>
				  (T.makeContext t ((T.termMatchPosition t ((T.makeContext t ((T.termMatchPosition t r))) r))), T.makeContext t ((T.termMatchPosition t r)), r, sigma) ) dmi
			      
	      (* デバック用 *)
	      (*val _ = print "dm(if s=variable,t=fun) \n"
	      val _ = dmToString1 (L.filter (fn r => checkDm (s,t) r) dm1)
	      val _ = dmToString (L.map (fn x => delsigma x) (L.filter (fn r => checkDm (s,t) r) dm1))*)
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
			  val _ = dmToString1 dm0*)
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
			  val _ = List.map (fn (c1,c2,r) => print ((" < " ^ (Term.toString (c1 term)) ^ "," ^ (Term.toString (c2 term)) ^ "," ^ (Term.toString r)) ^ " >,")) (L.map (fn x => delsigma x) dmi2)
			  val _ = print "\n"*)
			  (*val _ = print "dm2(if s=f(si),t=f(ti)) \n"
			  val _ = dmToString1 dm12*)
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
		      val _ = dmToString1 dm0*)
		  in
		      dm0
		  end
	  end
	      
	| dm (_,_) = []
			 
      val differenceMatching = L.filter (fn r => checkDm (t1,t2) r) (dm (t1,t2))
      (* デバッグ用 *)
      (*val _ = dmToString (L.map (fn x => delsigma x) differenceMatching)
      val _ = dmToString1 differenceMatching*)
   
  in
      differenceMatching
  end

(* maximal difference matching *)
val term = T.fromString "?hole" (* hole *)
val hole = (T.makeContext term nil, T.makeContext term nil, term)

fun MaxDm nil nil = [hole]
  | MaxDm nil ts = ts
  | MaxDm (x::xs) nil = MaxDm xs [x]
  | MaxDm ((c1,c2,r)::xs) (ts as ((c1',c2',r')::ys)) = 
    let 
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
    in 
	if size (erase (c1,c2,r), (c2 r)) = size (erase (c1',c2',r'), (c2' r')) then MaxDm xs (unionC (ts@[(c1,c2,r)],nil) term)
	else (if (size (erase (c1,c2,r) ,(c2 r))) < (size (erase (c1',c2',r'), (c2' r'))) then MaxDm xs [(c1,c2,r)]
	      else MaxDm xs ts)
    end

(* differenceMatchではないものをdelete*)
fun deleteNoDm ts =
    let
      fun wavehole (c1,c2,r) = r
      fun erase (c1,c2,r) = c1 (c2 r)
      val d = case (L.filter (fn t1 => not(erase t1 = wavehole t1)) ts) of 
		    nil => nil (*[hole] *)
		  | x => x
    in
	d
    end

(* (l0,r0)と差分があるようなルールを１つ見つける *)
fun isDif (l0,r0) nil = (nil,nil)
  | isDif (l0,r0) ((l1,r1)::rules) = 
    let 
	fun delsigma (c1,c2,r,sigma) = (c1,c2,r)
	val dmleft1 = deleteNoDm (L.map (fn x => delsigma x) (difMatch (l0,l1)))
	val dml1 = deleteNoDm (MaxDm dmleft1 nil)  (* maximal difference matching of left hand *) 
	val dmright1 = deleteNoDm (L.map (fn x => delsigma x) (difMatch (r0,r1)))
	val dmr1 = deleteNoDm (MaxDm dmright1 nil)  (* maximal difference matching of right hand *)
    in
	case (dml1,dmr1) of
	    (nil,_) => isDif (l0,r0) rules 
	  | (ls,rs) => (let
			   (*val _ = print (T.toString l1)
			   val _ = dmToString ls
			   val _ = print (T.toString r1)
			   val _ = dmToString rs*)
		       in
			   (ls,rs)
		       end)
    end       
end (* of local *)

end
