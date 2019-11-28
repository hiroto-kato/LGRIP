(* file: lemma.sml *)
(* lemma generation methods *)
(* author: Hiroto Kato *)

signature LEMMA =
sig 
    val genVar: Term.term * Term.term -> Comp.rules -> Comp.rules
    val generalize: Comp.rule -> Comp.rule
    val findBasicTerm: Trs.rule -> (Term.fun_key list * Term.fun_key list) -> Trs.rules
    val lemmagen: ManySorted.ms_rule * ManySorted.ms_rule -> ManySorted.ms_sign * Term.fun_key list -> ManySorted.ms_rules
    val lemmaGen1: ManySorted.ms_rule * ManySorted.ms_rule -> ManySorted.ms_sign * Term.fun_key list * Term.fun_key list -> (Trs.rule -> bool) -> int -> ManySorted.ms_rules
    val lemmaGen1Def: ManySorted.ms_rule * ManySorted.ms_rule -> ManySorted.ms_sign * Term.fun_key list * Term.fun_key list -> (Trs.rule -> bool) -> ManySorted.ms_rules
    val lemmaGen1Print: ManySorted.ms_rule * ManySorted.ms_rule -> ManySorted.ms_sign * Term.fun_key list * Term.fun_key list -> (Trs.rule -> bool) -> int ->  ManySorted.ms_rules
    val lemmaGen1PrintDef: ManySorted.ms_rule * ManySorted.ms_rule -> ManySorted.ms_sign * Term.fun_key list * Term.fun_key list -> (Trs.rule -> bool) -> ManySorted.ms_rules
end

structure Lemma:LEMMA = 
struct

local 
    structure L = List
    structure AL = AssocList
    structure LP = ListPair
    structure LU = ListUtil
    structure T = Term
    structure MS = ManySorted
    structure S = Symbol
in

exception noDifferenceMatch

(* 複数の同じ変数があれば一般化する *)
fun genVar (s,t) rs =
    let 
	(* 文字のアルファベットリスト little:97~122 big:65~90 *)
	fun alphlist 122 = [str (chr 90)]
	  | alphlist n = [str (chr n)]@(alphlist (n+1))
	(* 変数を一般化 *)
	fun f (v,nil) (l,r) rs = nil
	  | f (v,p::ps) (l,r) rs = 
	    let
		val vars = L.map (fn x => Var.toString x) (LU.union (T.vars s,T.vars t))
		val var = T.fromString (L.hd (LU.diff (alphlist 97,vars)))
		(* 左辺を一般化 *)
		val l1 = T.fillContext (T.makeContext s p) var
		(* 右辺の一般化できる変数の場所をそれぞれ一般化する *)
		val rpos = T.termMatchpos r v
		val rlist = L.map (fn p => T.fillContext (T.makeContext r p) var) rpos
		(* 補題の候補リスト *)
		val lrlist = L.map (fn r0 => (l1,r0)) rlist
		(* 両辺を書き換えたら同じものになるものを補題とする *)
		val rule = L.filter (fn (l0,r0) => Rewrite.linf rs r0 = Rewrite.linf rs l0) lrlist
	    in
		lrlist@(f (v,ps) (l,r) rs)
	    end
	val varTot = L.map (fn v => T.fromString (Var.toString v)) (T.vars s)
	val lvars = L.filter (fn (v,p) => not((L.length p)<2) ) (L.map (fn v => (v,T.termMatchpos s v)) varTot)
	val rules = L.concat (L.map (fn (v,p) => f (v,p) (s,t) rs) lvars)
    in
	rules
    end

fun generalize (l,r) =
  let
      (* 文字のアルファベットリスト little:97~122 big:65~90 *)
      fun alphlist 122 = [str (chr 122)]
	| alphlist n = [str (chr n)]@(alphlist (n+1))
      (* variable list *) 
      val varsl = L.map (fn x => T.fromString ("?" ^ (Var.toString x))) (T.vars l)
      val varsr = L.map (fn x => T.fromString ("?" ^ (Var.toString x))) (T.vars r)
      val funsl = L.map (fn x => T.fromString ("?" ^ (Fun.toString x))) (T.funs l)
      val funsr = L.map (fn x => T.fromString ("?" ^ (Fun.toString x))) (T.funs l)
      (* l -> r に使われているvariable以外の文字のvariableのリスト*)       
      val alphVar = LU.diff (L.map (fn str => T.fromString ("?" ^ str)) (alphlist 97), LU.union (varsl@varsr@funsl@funsr,nil))
      (* (term,poslist,t)からC[t]を作る *)
      fun makeContexts term nil t = T.fillContext (T.makeContext term nil) term
	| makeContexts term (x::xs) t = makeContexts (T.fillContext (T.makeContext term x) t) xs t
      (* l->rを与えられたtableを元に一般化する *)
      fun gen (l0,r0) ((t,v)::nil) = (makeContexts l0 (T.termMatchpos l0 t) v, makeContexts r0 (T.termMatchpos r0 t) v)
	| gen (l0,r0) ((t,v)::xs) = gen (makeContexts l0 (T.termMatchpos l0 t) v, makeContexts r0 (T.termMatchpos r0 t) v) (L.map (fn (x,y) => (makeContexts x (T.termMatchpos x t) v, y)) xs)
      (* subtermList *)
      val subl = LU.union (L.map (fn p => (T.subterm l p)) (T.pos l),nil)
      val subr = LU.union (L.map (fn p => (T.subterm r p)) (T.pos r),nil)
      val commonSub = L.concat (L.map (fn s => L.mapPartial (fn t => if s=t then SOME s else NONE) subl ) subr)
      val table = LP.zip (commonSub,alphVar)
  in
      gen (l,r) table
  end

(* dfun(cons,acc)を探す *)
fun findBasicTerm (s,t) (dfuns,cfuns) = 
  let 
      (* 文字のアルファベットリスト little:97~122 big:65~90 *)
      fun alphlist 122 = [str (chr 90)]
	| alphlist n = [str (chr n)]@(alphlist (n+1))
      val subl = L.map (fn x => T.subterm s x) (T.pos s)
      val basicTerml = LU.union (L.filter (fn x => T.isBasic (dfuns,cfuns) x) subl,nil)
      val matchTerml = L.filter (fn x => not (T.termMatchpos t x = nil)) basicTerml
      val trs1 = LP.map (fn (t,a) => (t,T.fromString ("??"^a))) (matchTerml,alphlist 97)
      val trs2 = L.map (fn t => (t,T.fromString ("??t"))) matchTerml
  in
      trs2
  end 

(* C[s]がConstructorのとき、D[C[s]]=D'[C[s]]をD[x]=D'[x]に一般化して補題を生成 *)
fun lemmagen (((l1,r1),ty1),((l2,r2),ty2)) (sign,cfuns) =
  let
      fun mkrules ( _ , nil) = nil
	| mkrules ((c1,c2,r),(c1',c2',l)::xs) =
	  let
	      val vl = LU.union (T.vars (c1 (c2 r)),T.vars (c1' (c2' l)))
	      val max = L.foldr (fn ((x,i),n) => Int.max (i,n)) 0 vl
	      val genterm = T.Var ("x",max+1)
	  in
	      (c1' genterm,c1 genterm)::(mkrules ((c1,c2,r),xs))
	  end

      fun toMsRule sign (l,r) =
	let
	    val sort = AL.find (Fun.fromString (Symbol.toString (T.root l))) sign
	    val rule = case sort of
			   NONE => NONE
			 | SOME (sortlist,sortkey) => SOME ((l,r),sortkey)
							   
	in
	    rule
	end
	    
      fun checkequal nil = nil
	| checkequal ((lr,ty)::rest) = if L.exists (fn lr0 => Trs.equal lr (MS.dropSortInMsRule lr0)) rest then checkequal rest
				       else (lr,ty)::(checkequal rest)
      (* 左辺の差分照合 *)
      val dmleft1 = L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((l1,ty1),(l2,ty2)))
      val dml1 = Dm_ms.MaxDm dmleft1 nil  (* maximal difference matching of left hand side*)
      (* 右辺の差分照合 *)    
      val dmright1 = L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((r1,ty1),(r2,ty2)))
      val dmr1 = Dm_ms.MaxDm dmright1 nil  (* maximal difference matching of right hand side*)

      (* (dm,dmset)のペアのリスト *)
      val dmg = L.map (fn (c1,c2,r) => ((c1,c2,r),L.filter (fn (c1',c2',l) => l=r andalso (c2 r) = (c2' l)) dmleft1)) dmright1
      val lemmas = L.concat (L.map (fn xs => mkrules xs) dmg)
      val msLemmas = checkequal (L.mapPartial (fn lr => toMsRule sign lr) lemmas)
      
      (* デバック用 *)
      (*val _ = print (Trs.prRules [(l1,r1),(l2,r2)])
      val _ = Subst.dmToString dmleft1
      val _ = Subst.dmToString dmright1
      val _ = print (Trs.prRules lemmas)
      val _ = print "-----------------------\n"*)
  in
      msLemmas
  end

(* ランダム補題生成手法 *)
fun lemmaGen1 (((l1,r1),ty1),((l2,r2),ty2)) (sign,dfuns,cfuns) grter n =
    let
	val hole = T.fromString "hole"
	(* holeを新しい変数にする関数 *)
	fun genhole c =
	    let
		val vl = LU.union (T.vars c,nil)
		val max = L.foldr (fn ((x,i),n) => Int.max (i,n)) 0 vl
		val genv = T.Var ("x",max+1)
	    in
		genv
	    end
		
	(* To a difference match from a difference match set*)
	fun toOp nil = NONE
	  | toOp (x::nil) = SOME x
	  | toOp (x::xs) = toOp xs
				
	(* a differece part *)
	fun dif (c1,c2,r) = c2 r
			       
	(* the size of a tree *) 
	fun size s = L.length (T.pos s)
	(* the depth of a tree *)
	fun depth s =
	    let
		fun maxListlen x nil = x
		  | maxListlen x (y::ys) = if (L.length x) > (L.length y) then maxListlen x ys
				       else maxListlen y ys
		val p = T.pos s
	    in
		L.length (maxListlen nil p)
	    end			    
		
	(* To many-sorted trs from trs*)
	fun toMsRule sign (l,r) =
	    let
		val sort = AL.find (Fun.fromString (Symbol.toString (T.root l))) sign
		val rule = case sort of
			       NONE => NONE
			     | SOME (sortlist,sortkey) => SOME ((l,r),sortkey)
							       
	    in
		rule
	    end
		
	fun checkequal nil = nil
	  | checkequal ((lr,ty)::rest) = if L.exists (fn lr0 => Trs.equal lr (MS.dropSortInMsRule lr0)) rest then checkequal rest
					 else (lr,ty)::(checkequal rest)
							   
	fun funOfGround sign0 nil = nil
	  | funOfGround sign0 (f::fl) = case MS.sortOfFun sign0 f of
					    ([],sortkey) => f::(funOfGround sign0 fl)
					  | (_,_) => funOfGround sign0 fl
								 
	(* 深さnまでランダムにルールの右辺を作成 *)
	fun makeRand (sign,vs,sort) fl [] _ = []
	  | makeRand (sign,vs,sort) fl tk 0 = tk
	  | makeRand (sign,vs,sort) fl tk n = 
	    let
		val funlenpair = L.map (fn f => case MS.sortOfFun sign f of
						    (m,sortkey) => (f,L.length m,sortkey)) fl
		val tk1 = L.concat (L.map (fn (f,len,key) => L.map (fn arg => (T.Fun (f,arg),key)) (LU.sequence (MS.dropSortInMsTerms tk) len []))  funlenpair)
		val tk2 = L.filter (fn (t,key) => T.isLinear t) tk1
		val tk3 = L.filter (fn (t,key) => key = sort) tk2
		val tkp = L.filter (fn t => case MS.sortInference sign [t] of
						NONE => false
					      | SOME env => L.all (fn x => LU.member x vs) env) tk3
	    in
		makeRand (sign,vs,sort) fl (tk@tkp) (n-1)
	    end
		
	fun makeRand2 (sign,vs,sort) fl [] _ = []
	  | makeRand2 (sign,vs,sort) fl tk 0 = tk
	  | makeRand2 (sign,vs,sort) fl tk n = 
	    let
		val funlenpair = L.map (fn f => case MS.sortOfFun sign f of
						    (m,sortkey) => (f,L.length m,sortkey)) fl
		val tk1 = L.concat (L.map (fn (f,len,key) => L.map (fn arg => (T.Fun (f,arg),key)) (LU.sequence (MS.dropSortInMsTerms tk) len []))  funlenpair)
		val tkx = L.filter (fn (t,key) => key = sort) tk1
		val tkp = L.filter (fn t => case MS.sortInference sign [t] of
						NONE => false
					      | SOME env => L.all (fn x => LU.member x vs) env) tkx
	    in
		makeRand2 (sign,vs,sort) fl (tk@tkp) (n-1)
	    end
		
	(* 左辺の差分照合 *)
	val dmleft1 = L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((l1,ty1),(l2,ty2)))
	val dml1 = Dm_ms.MaxDm dmleft1 nil  (* maximal difference matching of left hand side *)
	(* 右辺の差分照合 *)    
	val dmright1 = L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((r1,ty1),(r2,ty2)))
	val dmr1 = Dm_ms.MaxDm dmright1 nil  (* maximal difference matching of right hand side *)
			       
	(* 補題の左辺 *)
	val tempL1 = case toOp dml1 of
			 NONE => raise noDifferenceMatch
		       | SOME (c,c',t) => (if LU.member (T.root (c hole)) (T.toSymbol dfuns)
					      andalso L.exists (fn x => LU.member x cfuns) (T.funs (c hole))
					   then SOME (c (genhole (c hole)))
					   else if  LU.member (T.root (c (c' hole))) (T.toSymbol dfuns)
						    andalso L.exists (fn x => LU.member x cfuns) (T.funs (c (c' hole)))
					   then SOME (c (c' (genhole (c (c' hole)))))
					   else NONE)
					      
	(* 補題の右辺 (保留)*)
	val tempR = NONE (*case toOp dml1 of
		   	NONE => NONE
		      | SOME x =>   SOME (Dm_ms.skel x)*)
			
	(* main *)
	(* Basic Version*)
	val lems = case tempL1 of
		       NONE => []
		     | SOME templ => (let
					 (* the depth of tempL1, the size*)
					 val depthL = depth (valOf tempL1)  (* ランダム生成を行う深さ *)
					 val sizeL = size (valOf tempL1)
					 val gf = funOfGround sign (cfuns@dfuns) (* 0引数の関数記号集合 *)
					 val f = LU.diff (cfuns@dfuns,gf) (* 関数記号集合 *)
					 val sortL = MS.sortOfMsTerm (MS.toMsTerm sign templ) (* 左辺のソート *)
					 val vs = MS.sortAssignInMsTerm sign (MS.toMsTerm sign templ)  (* 左辺の変数集合 *)
					 val gfa = funOfGround sign (T.funs templ) (* 左辺にある0引数の関数集合 *)
					 val fa = LU.diff (T.funs templ,gf) (* 左辺にある0引数以外の関数集合 *)
					 val sortLa = MS.sortOfMsTerm (MS.toMsTerm sign templ) (* 左辺のソート *)
					 val vsa = MS.sortAssignInMsTerm sign (MS.toMsTerm sign templ)  (* 左辺の変数集合 *)
					 val t0a = case tempL1 of
						       NONE => []
						     | SOME x => (L.map (fn (v,k) => (T.fromString (Var.toString v),k)) vs)@(L.map (fn f => MS.toMsTerm sign (T.Fun (f,[]))) gfa) (* 深さ1のms_termの集合 *)
					 val temptm = if n=0 then makeRand (sign,vs,sortLa) fa t0a depthL (* Default-左辺の深さまで *)
						      else makeRand (sign,vs,sortLa) fa t0a n (* 深さnまで *)
					 val temprls = L.map (fn (t,key) => ((valOf tempL1,t),key)) temptm
					 val tempLem = case tempR of
							   NONE => temprls
							 | SOME termR => (if T.isVar termR then temprls else L.filter (fn ((l,r),ty) => (T.root r) = (T.root termR)) temprls)
				     in
					 L.filter (fn (lr,ty) => grter lr) tempLem
				     end)
    in
	lems
    end

(* ランダム補題生成手法 Depth Default *)
fun lemmaGen1Def (((l1,r1),ty1),((l2,r2),ty2)) (sign,dfuns,cfuns) grter = lemmaGen1 (((l1,r1),ty1),((l2,r2),ty2)) (sign,dfuns,cfuns) grter 0
    
(* ランダム補題生成手法 ~Debug Version~ *)
fun lemmaGen1Print (((l1,r1),ty1),((l2,r2),ty2)) (sign,dfuns,cfuns) grter n =
    let
	val hole = T.fromString "hole"
	(* holeを新しい変数にする関数 *)
	fun genhole c =
	    let
		val vl = LU.union (T.vars c,nil)
		val max = L.foldr (fn ((x,i),n) => Int.max (i,n)) 0 vl
		val genv = T.Var ("x",max+1)
	    in
		genv
	    end
		
	(* To a difference match from a difference match set*)
	fun toOp nil = NONE
	  | toOp (x::nil) = SOME x
	  | toOp (x::xs) = toOp xs
				
	(* a differece part *)
	fun dif (c1,c2,r) = c2 r
			       
	(* the size of a tree *) 
	fun size s = L.length (T.pos s)
	(* the depth of a tree *)
	fun depth s =
	    let
		fun maxListlen x nil = x
		  | maxListlen x (y::ys) = if (L.length x) > (L.length y) then maxListlen x ys
					   else maxListlen y ys
		val p = T.pos s
	    in
		L.length (maxListlen nil p)
	    end
		
	(* To many-sorted trs from trs*)
	fun toMsRule sign (l,r) =
	    let
		val sort = AL.find (Fun.fromString (Symbol.toString (T.root l))) sign
		val rule = case sort of
			       NONE => NONE
			     | SOME (sortlist,sortkey) => SOME ((l,r),sortkey)
							       
	    in
		rule
	    end
		
	fun checkequal nil = nil
	  | checkequal ((lr,ty)::rest) = if L.exists (fn lr0 => Trs.equal lr (MS.dropSortInMsRule lr0)) rest then checkequal rest
					 else (lr,ty)::(checkequal rest)
							   
	fun funOfGround sign0 nil = nil
	  | funOfGround sign0 (f::fl) = case MS.sortOfFun sign0 f of
					    ([],sortkey) => f::(funOfGround sign0 fl)
					  | (_,_) => funOfGround sign0 fl
								 
	(* 深さnまでランダムにルールの右辺を作成 *)
	fun makeRand (sign,vs,sort) fl [] _ = []
	  | makeRand (sign,vs,sort) fl tk 0 = tk
	  | makeRand (sign,vs,sort) fl tk n = 
	    let
		val funlenpair = L.map (fn f => case MS.sortOfFun sign f of
						    (m,sortkey) => (f,L.length m,sortkey)) fl
		val tk1 = L.concat (L.map (fn (f,len,key) => L.map (fn arg => (T.Fun (f,arg),key)) (LU.sequence (MS.dropSortInMsTerms tk) len []))  funlenpair)
		val tk2 = L.filter (fn (t,key) => T.isLinear t) tk1
		val tk3 = L.filter (fn (t,key) => key = sort) tk2
		val tkp = L.filter (fn t => case MS.sortInference sign [t] of
						NONE => false
					      | SOME env => L.all (fn x => LU.member x vs) env) tk3
	    in
		makeRand (sign,vs,sort) fl (tk@tkp) (n-1)
	    end
		
	(* 左辺の差分照合 *)
	val dmleft1 = L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((l1,ty1),(l2,ty2)))
	val dml1 = Dm_ms.MaxDm dmleft1 nil  (* maximal difference matching of left hand side *)
	(* 右辺の差分照合 *)    
	val dmright1 = L.map (fn x => Dm_ms.delSigma x) (Dm_ms.msDifMatch sign ((r1,ty1),(r2,ty2)))
	val dmr1 = Dm_ms.MaxDm dmright1 nil  (* maximal difference matching of right hand side *)
			       
	(* 補題の左辺 *)
	val tempL1 = case toOp dml1 of
			 NONE => raise noDifferenceMatch
		       | SOME (c,c',t) => (if LU.member (T.root (c hole)) (T.toSymbol dfuns)
					      andalso L.exists (fn x => LU.member x cfuns) (T.funs (c hole))
					   then SOME (c (genhole (c hole)))
					   else if  LU.member (T.root (c (c' hole))) (T.toSymbol dfuns)
						    andalso L.exists (fn x => LU.member x cfuns) (T.funs (c (c' hole)))
					   then SOME (c (c' (genhole (c (c' hole)))))
					   else NONE)
					      
	(* 補題の右辺 *)
	val tempR = NONE(*case toOp dmr1 of
		      NONE => NONE  
		    | SOME x => SOME	 (Dm_ms.skel x)*)
			
	(* main *)
	(* Basic Version*)
	val lems = case tempL1 of
		       NONE => []
		     | SOME templ => (let
					 (* the depth of tempL1, the size*)
					 val depthL = depth (valOf tempL1)
					 val sizeL = size (valOf tempL1)
					 val gf = funOfGround sign (cfuns@dfuns) (* 0引数の関数記号集合 *)
					 val f = LU.diff (cfuns@dfuns,gf) (* 関数記号集合 *)
					 val sortL = MS.sortOfMsTerm (MS.toMsTerm sign templ) (* 左辺のソート *)
					 val vs = MS.sortAssignInMsTerm sign (MS.toMsTerm sign templ)  (* 左辺の変数集合 *)
					 val gfa = funOfGround sign (T.funs templ) (* 左辺にある0引数の関数集合 *)
					 val fa = LU.diff (T.funs templ,gf) (* 左辺にある0引数以外の関数集合 *)
					 val sortLa = MS.sortOfMsTerm (MS.toMsTerm sign templ) (* 左辺のソート *)
					 val vsa = MS.sortAssignInMsTerm sign (MS.toMsTerm sign templ)  (* 左辺の変数集合 *)
					 val t0a = case tempL1 of
						       NONE => []
						     | SOME x => (L.map (fn (v,k) => (T.fromString (Var.toString v),k)) vs)@(L.map (fn f => MS.toMsTerm sign (T.Fun (f,[]))) gfa) (* 深さ1のms_termの集合 *)
					 val temptm = if n=0 then makeRand (sign,vs,sortLa) fa t0a depthL (* Default-左辺の深さまで *)
						      else makeRand (sign,vs,sortLa) fa t0a n (* 深さnまで *)
					 val temprls = L.map (fn (t,key) => ((valOf tempL1,t),key)) temptm
					 val tempLem = case tempR of
							   NONE => temprls
							 | SOME termR => (if T.isVar termR then temprls else L.filter (fn ((l,r),ty) => (T.root r) = (T.root termR)) temprls)
				     in
					 L.filter (fn (lr,ty) => grter lr) tempLem
				     end)
					 
	(* debug *)
	val _ = print "\nDivergence series\n"
	val _ = print (Trs.prRules [(l1,r1),(l2,r2)])
	val _ = print "Difference Match\n"
	val _ = Subst.dmToString dml1
	val _ = Subst.dmToString dmr1
	val _ = print "Temp lemma : \n"
	val _ = case (tempL1,tempR) of (NONE,NONE) => print " []\n"
				     | (SOME templ,NONE) => print (Trs.prEqs [(templ,Term.fromString "?t")])
	val _ = print "Depth : "
	val _ = if n=0 then case tempL1 of NONE => print "\n"
					 | SOME templ => print ((Int.toString (depth templ)) ^ "\n")
		else print ((Int.toString n) ^ "\n")
    in
	lems
    end
	
(* ランダム補題生成手法 ~Debug Version~ Depth Default *)
fun lemmaGen1PrintDef (((l1,r1),ty1),((l2,r2),ty2)) (sign,dfuns,cfuns) grter = lemmaGen1Print (((l1,r1),ty1),((l2,r2),ty2)) (sign,dfuns,cfuns) grter 0
											   
end (* of local *)
end (* of struct *)
