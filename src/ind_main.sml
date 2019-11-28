(* File: ind_main.sml *)
(* Main function : Inductive theorem prover with disproof in many-sorted TRS *)
(* author: Hiroto Kato *)

signature INDMAIN =
sig
    val indPars: string -> ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) * ManySorted.ms_eqs
    val proc2nd: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) * ManySorted.ms_eqs -> int * int -> ManySorted.ms_eqs -> bool
    val proc: string -> int -> bool
    val procDef: string -> bool
    val procPrint: string -> int -> bool
    val procPrintDef: string -> bool
    val proc_Nolemgen: string -> int -> bool
    val proc_NolemgenDef: string -> bool
    val proc_NolemgenPrint: string -> int -> bool
    val proc_NolemgenPrintDef: string -> bool
    val procDepth2nd: ManySorted.ms_sign * ManySorted.ms_rules * (Trs.rule -> bool) * ManySorted.ms_eqs -> int * int -> ManySorted.ms_eqs -> int -> bool					     
    val procDepth : string -> int -> int -> bool
    val procDepthDef : string -> int -> bool
    val procDepthPrint : string -> int -> int -> bool
    val procDepthPrintDef : string -> int -> bool
    val procDepth_Nolemgen : string -> int -> int -> bool
    val procDepth_NolemgenDef : string -> int -> bool
    val procDepth_NolemgenPrint : string -> int -> int -> bool
    val procDepth_NolemgenPrintDef : string -> int -> bool
    val procLemmas : string -> bool
    val procDepthLemmas : string -> int -> bool
end 

structure IndMain:INDMAIN = 
struct

local 
    structure L = List
    structure AL = AssocList
    structure LP = ListPair
    structure LU = ListUtil
    structure T = Term
    structure MS = ManySorted
    structure S = String
in

exception Failure
exception Stopped
exception Success
exception Disproof
	      
(* induction parsing *)
fun indPars str0 =
  let
      
      (* 文字列sとtの間の文字列リストを返す *)
      fun parsl (s,t) (x::xs) = if x=s then (parsll t xs)
				else (parsl (s,t) xs)
      and parsll t (l::ls) = if l=t then []
				else [l]@(parsll t ls)
      (* 文字列を"(",")",","で分けた文字列リストにする *)
      fun pars (nil,nil) ss = L.rev ss
	| pars (nil,ls) ss = pars (nil,nil) ((String.implode (L.rev ls))::ss)
	| pars (c::cl,nil) nil = if (c = #"(" orelse c = #")" orelse c = #",")
				 then pars (cl,nil) ((String.str c)::nil)
				 else pars (cl,[c]) nil
	| pars (c::cl,nil) ss = if (c = #"(" orelse c = #")" orelse c = #",")
				then pars (cl,nil) ((String.str c)::ss)
				else pars (cl,[c]) ss
	| pars (c::cl,ls) ss = if (c = #"(" orelse c = #")" orelse c = #",")
			       then pars (cl,nil) ((String.str c)::(String.implode (L.rev ls))::ss)
			       else pars (cl,c::ls) ss

      (* ruleやeqsのstring listにおいて、変数を見つける(変数の前に?をつける) *)
      fun toVar strl funl = L.map (fn s =>
				      if (L.exists (fn x => s=x) (funl@[")","(",","]))
				      then s else ("?"^s))  strl

      (* rule string listとfunction string listを渡して、trsを返す *)
      fun ruleVar str funstr=
	let
	    val rcharl = L.map (fn (s,t) => (String.explode (T.toString s), String.explode (T.toString t))) (L.map Trs.rdRule str)
	    val rulepars = L.map (fn (s,t) => (pars (s,nil) nil, pars (t,nil) nil)) rcharl
	    val rules = L.map (fn (s,t) => (T.fromString (String.concat (toVar s funstr)), T.fromString (String.concat (toVar t funstr))) ) rulepars 
	in
	    rules
	end

      (* es string listとfunction string listを渡して、trsを返す *)
      fun esVar str funstr=
	let
	    val escharl = L.map (fn (s,t) => (String.explode (T.toString s), String.explode (T.toString t))) (L.map Trs.rdEq str)
	    val espars = L.map (fn (s,t) => (pars (s,nil) nil, pars (t,nil) nil)) escharl
	    val es = L.map (fn (s,t) => (T.fromString (String.concat (toVar s funstr)), T.fromString (String.concat (toVar t funstr))) ) espars 
	in
	    es
	end

      (* from TRS to many-sorted TRS *)
      fun toMsRule sign (l,r) =
	let
	    val sort = AL.find (Fun.fromString (Symbol.toString (T.root l))) sign
	    val rule = case sort of
			   NONE => NONE
			 | SOME (sortlist,sortkey) => SOME ((l,r),sortkey)
							   
	in
	    rule
	end

      (* (+ Nat Nat -> Nat) => +:Nat,Nat -> Nat *)
      fun toSign str =
	let
	    (* (を削除 *)
	    fun foo0 (x::xs) = [(S.implode (L.tl (S.explode x)))]@xs
	      (* )を削除 *)						      
	    fun foo1 (x::nil) = (S.implode (L.rev (L.tl (L.rev (S.explode x)))))::nil
	      | foo1 (x::xs) = x::(foo1 xs)
	    (* ,を追加 *)
	    fun foo2 (x::xs) =
	      let
		  fun subfoo2 (y::ys) = case y of
					    "->" => ys
					  | _ => if L.hd ys = "->" then y::ys
						 else y::","::(subfoo2 ys)
	      in
		  x::(subfoo2 xs)
	      end
	    (* : を追加 *)		
	    fun foo3 (x::xs) = x::":"::xs
					   
	    val xs = foo3 (foo2 (foo1 (foo0 (S.tokens (fn x => x = #" ") str))))
	in
	    xs
	end
	    
      val dir = ""
      val path = dir ^ str0
      val file = TextIO.openIn(path)
      val str1 = TextIO.inputAll file
      val strl1 = String.tokens (fn x => x = #"\n") str1

      (* FUN or フォーマットがmstrsのときSIG*)
      val sortfunstrl = L.map toSign (parsl ("(SIG",")") strl1)
      val sortfunstr = L.map S.concat sortfunstrl
      val funstrl = L.map L.hd sortfunstrl (* function string list *)
      (*val funstrl = L.map (fn x => L.hd (String.tokens (fn y => y = #" ") x)) funstr (* function string list *)*)
      val rulestrl = parsl ("(RULES",")") strl1 (* rule string list *)
      val eqstrl = parsl ("(CONJECTURES",")") strl1 (* equation string list *)

      (* rs: trs, es: (term*term) list *)
      val sign = L.map (fn x => MS.rdMsFun x) sortfunstr
      val rs = ruleVar rulestrl funstrl
      val es = esVar eqstrl funstrl
      val msrs = L.mapPartial (fn x => toMsRule sign x) rs
      val mses = L.mapPartial (fn x => toMsRule sign x) es
      val _ = print "-------------------------------------------------------------------------\n"
      val _ = print "SIG:"
      val _ = print (MS.prMsFuns sign)
      val _ = print "TRS:"
      val _ = print (Trs.prRules rs)
      val _ = print "Eqs:"			    
      val _ = print (Trs.prEqs es)
      val _ = print "-------------------------------------------------------------------------\n\n"
		    
      (* PathOrder *)

      fun lpostr (rs,lpol) = 
	let
	    open Formula
	    (* 関数記号と重み変数のテーブル *)
	    val funs = L.foldr (fn ((l,r),fs) => LU.union (T.funs l, LU.union (T.funs r, fs))) [] rs
	    val vars = L.tabulate (L.length funs, fn x => Var x)
	    val table = LP.zip (funs, vars)
	    fun lookup f = valOf (AL.find f table)
	    fun prec (f,g) = Atom (Gt (lookup f, lookup g))

	    fun encodeOrder ((f1,w1), []) = []
	      | encodeOrder ((f1,w1), ((f2,w2)::xs)) = if w1=w2 then encodeOrder ((f1,w1),xs)
						       else (if w1 > w2 then [Not (Atom (Gt (valOf (AL.find f1 table), valOf (AL.find f2 table))))]@(encodeOrder ((f1,w1), xs))
							     else encodeOrder ((f1,w1),xs))
	    (* LPO termination のエンコーディング *)
	    val propGe0 = Conj (L.map (fn (_,x) => Atom (Ge (x, Const 0))) table)
	    val propDist = Atom (Distinct (L.map (fn (_,x) => x) table))
	    (*indを実行して失敗した時のorderの集合*)
(*	    val propNotLpo = Conj (L.map (fn x => Disj (L.concat (L.map (fn (f,w) => (encodeOrder ((f,w), x))) x))) lpol)*)
	    val propLpo = Conj (L.map (fn (s,t) => PathOrder.encodeLpoGt prec (s,t)) rs)
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

	    (* display lpo *)
	    (*val _ = print "\n"
	    val _ = print "\n\tLpo\n"
	    val _ = case Yices2.runSolver lpoTerminationInquiry of
			SOME assig =>
			let
			    val _ = L.app (fn (f,x) => print ("\t" ^ f ^ ":" ^ (Int.toString (valOf (AL.find (Yices2.prArith x) assig))) ^ "\n")) table	  
			in true
			end
		      | NONE => false*)
	     
	in
	    case Yices2.runSolver lpoTerminationInquiry of
		SOME assig => L.map (fn (f,x) => (f, (valOf (AL.find (Yices2.prArith x) assig)))) table
	      | NONE => (print "lpo no Termination\n";raise Failure)
	end

      val lpo = lpostr (rs,nil)
      val grter = PathOrder.lpoGt (PathOrder.rdPrec lpo)

      (* 追加 *)
      fun main (sign,rs,es) lpol =
	let 
	    val lpo0 = lpostr (MS.dropSortInMsRules rs,lpol)
	    val grter0 = PathOrder.lpoGt (PathOrder.rdPrec lpo0)
	in
	    IndMs.ind (sign,rs,grter0) es
	    handle ExpandFailure => (main (sign,rs,es) (lpol@[lpo0]))
	end
	    
  in
      (*IndMs.ind (sign,msrs,grter) mses*)
      (sign,msrs,grter,mses)
  end

(* 補題の証明プロセス *)
fun proc2nd (sign,rs,grter,es) (n,max) tmp = if n>max then raise Stopped else 
  let
      fun toleft (x,y) = x
      val prop = IndMs.ind (sign,rs,grter) es max 
      val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGen (sign,rs,grter) es, nil)) (*LemGen.lemGenNoPrint (sign,rs,grter) es*)
		   else []
      val soundlemmas = if prop = "Stopped" then L.filter (fn e => proc2nd (sign,rs,grter,[e]) (n+1,max) (LU.union (tmp,es))) lemmas
			else []
      val randlem = if soundlemmas = [] then (if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDef (sign,rs,grter) es,nil))
					      else [])
		    else []

      val randomlemmas = if soundlemmas = [] then (if prop = "Stopped"
						   then L.filter (fn e => proc2nd (sign,rs,grter,[e]) (n+1,max) (LU.union (tmp,es))) randlem
						   else [])
			 else []
				  
      val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
      (*val max = 6*)
  in
      if n > max  then raise Stopped
      else
	  if prop="Success" then true
	  else if prop = "Disproof" then false
	  else if prop = "Failed" then false
	  else (if prop = "Stopped" andalso lemmas0 = [] then raise Failure
		else proc2nd (sign,rs,grter,LU.union (es,lemmas0)) (n+1,max) (LU.union (es,lemmas0)))
  end handle Success => true
	   | Failure => false
	   | Stopped => false
	   | Disproof => false
			     
(* Main Process *)
fun proc str max =
    let
	val (sign0,rs0,grter0,es0) = indPars str
					     
	fun procSub (sign,rs,grter,es) n lem =
	    let
		fun toleft (x,y) = x
		val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
		val prop = IndMs.ind (sign,rs,grter) es max 
		val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nLemma Generation:" else print ""
		(* Difference MatchとNew Lemma Generationの手続き *)
		val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGen (sign,rs,grter) es,nil))
			     else []
		val soundlemmas = if prop = "Stopped" then L.filter (fn e => proc2nd (sign,rs,grter,[e]) (1,max) [e]) lemmas
				  else []
		(* 証明された補題の表示 *)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules soundlemmas)))
			  | _  => print ""
					
		val _ = case  prop  of
			    "Stopped" => if soundlemmas = [] then print "Random Lemma Generation:" else print ""
			  | _  => print ""
		(* Random Lemma Generationの手続き *)
		val randlem = case prop of
				  "Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDef (sign,rs,grter) es,nil))
					       else []
				| _ => []
		val randomlemmas = case prop of
				       "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => proc2nd (sign,rs,grter,[e]) (1,max) [e]) randlem)
						     else [])
				     | _  => []
		(* ランダム補題生成の補題の個数 *)
		val _ = if randlem = [] then print ""
			else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
		(* 証明された補題の表示 *)
		(*val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules randomlemmas))))
					 else print ""
			  | _ => print ""*)
				   
		val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
					 else print ""
			  | _ => print ""
		(*val max = 6*)
	    in
		if n > max  then raise Stopped
		else
		    case prop of
			"Success" => (let
					 val _ = print "Lemmas:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
					 val _ = print "Proved:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsRules es0))
					 val _ = print "Success\n"
				     in
					 true
				     end )
		      | "Disproof" => ((print ("Disproof:" ^ (Trs.prEqs (MS.dropSortInMsRules es))));false)
		      | "Failed" => ((print "Failed\n");false)
		      | "Stopped" => if lemmas0 = [] then (print "We cannot find lemmas.\n"; raise Failure)
 				     else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		      | _ => false
				 
	    end handle Success => (print "Success\n"; true)
		     | Failure => (print "Failed\n"; false)
		     | Stopped => (print "Stopped\n"; false)
		     | Disproof => (print "Conjectures are non-Inductive Theorems\n"; false)
    in
	procSub (sign0,rs0,grter0,es0) 1 []
    end

(* Main Process-Defoult Version*)
fun procDef str = proc str 6

(* ~Debug Version~ *)
fun procPrint str max =
    let
	val (sign0,rs0,grter0,es0) = indPars str
					     
	fun procSub (sign,rs,grter,es) n lem =
	    let
		fun toleft (x,y) = x
		val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
		val prop = IndMs.ind (sign,rs,grter) es max 
		val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nLemma Generation:" else print ""
		(* Difference MatchとNew Lemma Generationの手続き *)
		val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGenPrint (sign,rs,grter) es,nil))
			     else []
		val soundlemmas = if prop = "Stopped" then L.filter (fn e => proc2nd (sign,rs,grter,[e]) (1,max) [e]) lemmas
				  else []
		(* 証明された補題の表示 *)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then print "\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules soundlemmas)))
			  | _  => print ""
					
		val _ = case  prop  of
			    "Stopped" => if soundlemmas = [] then print "Random Lemma Generation:" else print ""
			  | _  => print ""
		(* Random Lemma Generationの手続き *)
		val randlem = case prop of
				  "Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDefPrint (sign,rs,grter) es,nil))
					       else []
				| _ => []
		val randomlemmas = case prop of
				       "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => proc2nd (sign,rs,grter,[e]) (1,max) [e]) randlem)
						     else [])
				     | _  => []
		(* ランダム補題生成の補題の個数 *)
		val _ = if randlem = [] then print ""
			else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
		(* 証明された補題の表示 *)
		(*val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules randomlemmas))))
					 else print ""
			  | _ => print ""*)
				   
		val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
					 else print ""
			  | _ => print ""
		(*val max = 6*)
	    in
		if n > max  then raise Stopped
		else
		    case prop of
			"Success" => (let
					 val _ = print "Lemmas:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
					 val _ = print "Proved:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsRules es0))
					 val _ = print "Success\n"
				     in
					 true
				     end )
		      | "Disproof" => ((print ("Disproof:" ^ (Trs.prEqs (MS.dropSortInMsRules es))));false)
		      | "Failed" => ((print "Failed\n");false)
		      | "Stopped" => if lemmas0 = [] then (print "We cannot find lemmas.\n"; raise Failure)
 				     else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		      | _ => false
				 
	    end handle Success => (print "Success\n"; true)
		     | Failure => (print "Failed\n"; false)
		     | Stopped => (print "Stopped\n"; false)
		     | Disproof => (print "Conjectures are non-Inductive Theorems\n"; false)
    in
	procSub (sign0,rs0,grter0,es0) 1 []
    end

(* ~Debug Version~ Default Version *)
fun procPrintDef str = procPrint str 6

(* 補題の証明に補題を用いない Main Process *)
fun proc_Nolemgen str max =
    let
	val (sign0,rs0,grter0,es0) = indPars str
					     
	fun procSub (sign,rs,grter,es) n lem =
	    let
		fun toleft (x,y) = x
		val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
		val prop = IndMs.ind (sign,rs,grter) es max
		val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nLemma Generation:" else print ""
		(* Difference MatchとNew Lemma Generationの手続き *)
		val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGen (sign,rs,grter) es,nil))
			     else []
		val soundlemmas = if prop = "Stopped" then L.filter (fn e => (IndMs.ind (sign,rs,grter) [e] max) = "Success") lemmas
				  else []
		(* 証明された補題の表示 *)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules soundlemmas)))
			  | _  => print ""
					
		val _ = case  prop  of
			    "Stopped" => if soundlemmas = [] then print "Random Lemma Generation:" else print ""
			  | _  => print ""
		(* Random Lemma Generationの手続き *)
		val randlem = case prop of
				  "Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDef (sign,rs,grter) es,nil))
					       else []
				| _ => []
		val randomlemmas = case prop of
				       "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => (IndMs.ind (sign,rs,grter) [e] max) = "Success") randlem)
						     else [])
				     | _  => []
		(* ランダム補題生成の補題の個数 *)
		val _ = if randlem = [] then print ""
			else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
		(* 証明された補題の表示 *)
		(*val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules randomlemmas))))
					 else print ""
			  | _ => print ""*)
				   
		val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
					 else print ""
			  | _ => print ""
		(*val max = 6*)
	    in
		if n > max  then raise Stopped
		else
		    case prop of
			"Success" => (let
					 val _ = print "Lemmas:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
					 val _ = print "Proved:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsRules es0))
					 val _ = print "Success\n"
				     in
					 true
				     end )
		      | "Disproof" => ((print ("Disproof:" ^ (Trs.prEqs (MS.dropSortInMsRules es))));false)
		      | "Failed" => ((print "Failed\n");false)
		      | "Stopped" => if lemmas0 = [] then (print "We cannot find lemmas.\n"; raise Failure)
 				     else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		      | _ => false
				 
	    end handle Success => (print "Success\n"; true)
		     | Failure => (print "Failed\n"; false)
		     | Stopped => (print "Stopped\n"; false)
		     | Disproof => (print "Conjectures are non-Inductive Theorems\n"; false)
    in
	procSub (sign0,rs0,grter0,es0) 1 []
    end

(* 補題の証明に補題を用いない Main Process-Default *)
fun proc_NolemgenDef str = proc_Nolemgen str 6
					 
(* 補題の証明に補題を用いない ~Debug Version~ *)
fun proc_NolemgenPrint str max =
    let
	val (sign0,rs0,grter0,es0) = indPars str
					     
	fun procSub (sign,rs,grter,es) n lem =
	    let
		fun toleft (x,y) = x
		val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
		val prop = IndMs.ind (sign,rs,grter) es max 
		val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nLemma Generation:" else print ""
		(* Difference MatchとNew Lemma Generationの手続き *)
		val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGenPrint (sign,rs,grter) es,nil))
			     else []
		val soundlemmas = if prop = "Stopped" then L.filter (fn e => (IndMs.ind (sign,rs,grter) [e] max) = "Success") lemmas
				  else []
		(* 証明された補題の表示 *)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then print "\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules soundlemmas)))
			  | _  => print ""
					
		val _ = case  prop  of
			    "Stopped" => if soundlemmas = [] then print "Random Lemma Generation:" else print ""
			  | _  => print ""
		(* Random Lemma Generationの手続き *)
		val randlem = case prop of
				  "Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDefPrint (sign,rs,grter) es,nil))
					       else []
				| _ => []
		val randomlemmas = case prop of
				       "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => (IndMs.ind (sign,rs,grter) [e] max) = "Success") randlem)
						     else [])
				     | _  => []
		(* ランダム補題生成の補題の個数 *)
		val _ = if randlem = [] then print ""
			else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
		(* 証明された補題の表示 *)
		(*val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules randomlemmas))))
					 else print ""
			  | _ => print ""*)
				   
		val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
					 else print ""
			  | _ => print ""
		(*val max = 6*)
	    in
		if n > max  then raise Stopped
		else
		    case prop of
			"Success" => (let
					 val _ = print "Lemmas:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
					 val _ = print "Proved:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsRules es0))
					 val _ = print "Success\n"
				     in
					 true
				     end )
		      | "Disproof" => ((print ("Disproof:" ^ (Trs.prEqs (MS.dropSortInMsRules es))));false)
		      | "Failed" => ((print "Failed\n");false)
		      | "Stopped" => if lemmas0 = [] then (print "We cannot find lemmas.\n"; raise Failure)
 				     else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		      | _ => false
				 
	    end handle Success => (print "Success\n"; true)
		     | Failure => (print "Failed\n"; false)
		     | Stopped => (print "Stopped\n"; false)
		     | Disproof => (print "Conjectures are non-Inductive Theorems\n"; false)
    in
	procSub (sign0,rs0,grter0,es0) 1 []
    end

(* 補題の証明に補題を用いない ~Debug Version~ Default*)
fun proc_NolemgenPrintDef str = proc_NolemgenPrint str 6


(* 補題の証明プロセス(深さ入力) *)
fun procDepth2nd (sign,rs,grter,es) (n,max) tmp depth = if n>max then raise Stopped else 
  let
      fun toleft (x,y) = x
      val prop = IndMs.ind (sign,rs,grter) es max 
      val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGen (sign,rs,grter) es, nil)) (*LemGen.lemGenNoPrint (sign,rs,grter) es*)
		   else []
      val soundlemmas = if prop = "Stopped" then L.filter (fn e => procDepth2nd (sign,rs,grter,[e]) (n+1,max) (LU.union (tmp,es)) depth) lemmas
			else []
      val randlem = if soundlemmas = [] then (if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDepth (sign,rs,grter) es depth,nil))
					      else [])
		    else []

      val randomlemmas = if soundlemmas = [] then (if prop = "Stopped"
						   then L.filter (fn e => procDepth2nd (sign,rs,grter,[e]) (n+1,max) (LU.union (tmp,es)) depth) randlem
						   else [])
			 else []
				  
      val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
  in
      if n > max  then raise Stopped
      else
	  if prop="Success" then true
	  else if prop = "Disproof" then false
	  else if prop = "Failed" then false
	  else (if prop = "Stopped" andalso lemmas0 = [] then raise Failure
		else procDepth2nd (sign,rs,grter,LU.union (es,lemmas0)) (n+1,max) (LU.union (es,lemmas0)) depth )
  end handle Success => true
	   | Failure => false
	   | Stopped => false
	   | Disproof => false

(* Main Process (深さ入力) *)
fun procDepth str max depth =
    let
	val (sign0,rs0,grter0,es0) = indPars str
					     
	fun procSub (sign,rs,grter,es) n lem =
	    let
		fun toleft (x,y) = x
		val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
		val prop = IndMs.ind (sign,rs,grter) es max 
		val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nLemma Generation:" else print ""
		(* Difference MatchとNew Lemma Generationの手続き *)
		val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGen (sign,rs,grter) es,nil))
			     else []
		val soundlemmas = if prop = "Stopped" then L.filter (fn e => procDepth2nd (sign,rs,grter,[e]) (1,max) [e] depth) lemmas
				  else []
		(* 証明された補題の表示 *)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules soundlemmas)))
			  | _  => print ""
					
		val _ = case  prop  of
			    "Stopped" => if soundlemmas = [] then print "Random Lemma Generation:" else print ""
			  | _  => print ""
		(* Random Lemma Generationの手続き *)
		val randlem = case prop of
				  "Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDepth (sign,rs,grter) es depth,nil))
					       else []
				| _ => []
		val randomlemmas = case prop of
				       "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => procDepth2nd (sign,rs,grter,[e]) (1,max) [e] depth) randlem)
						     else [])
				     | _  => []
		(* ランダム補題生成の補題の個数 *)
		val _ = if randlem = [] then print ""
			else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
		(* 証明された補題の表示 *)
		(*val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules randomlemmas))))
					 else print ""
			  | _ => print ""*)
				   
		val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
					 else print ""
			  | _ => print ""
		(*val max = 6*)
	    in
		if n > max  then raise Stopped
		else
		    case prop of
			"Success" => (let
					 val _ = print "Lemmas:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
					 val _ = print "Proved:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsRules es0))
					 val _ = print "Success\n"
				     in
					 true
				     end )
		      | "Disproof" => ((print ("Disproof:" ^ (Trs.prEqs (MS.dropSortInMsRules es))));false)
		      | "Failed" => ((print "Failed\n");false)
		      | "Stopped" => if lemmas0 = [] then (print "We cannot find lemmas.\n"; raise Failure)
 				     else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		      | _ => false
				 
	    end handle Success => (print "Success\n"; true)
		     | Failure => (print "Failed\n"; false)
		     | Stopped => (print "Stopped\n"; false)
		     | Disproof => (print "Conjectures are non-Inductive Theorems\n"; false)
    in
	procSub (sign0,rs0,grter0,es0) 1 []
    end

fun procDepthDef str depth = procDepth str 6 depth

(*(深さ入力) ~Debug Version~ *)
fun procDepthPrint str max depth =
    let
	val (sign0,rs0,grter0,es0) = indPars str
					     
	fun procSub (sign,rs,grter,es) n lem =
	    let
		fun toleft (x,y) = x
		val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
		val prop = IndMs.ind (sign,rs,grter) es max 
		val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nLemma Generation:" else print ""
		(* Difference MatchとNew Lemma Generationの手続き *)
		val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGenPrint (sign,rs,grter) es,nil))
			     else []
		val soundlemmas = if prop = "Stopped" then L.filter (fn e => procDepth2nd (sign,rs,grter,[e]) (1,max) [e] depth) lemmas
				  else []
		(* 証明された補題の表示 *)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then print "\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules soundlemmas)))
			  | _  => print ""
					
		val _ = case  prop  of
			    "Stopped" => if soundlemmas = [] then print "Random Lemma Generation:" else print ""
			  | _  => print ""
		(* Random Lemma Generationの手続き *)
		val randlem = case prop of
				  "Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDepthPrint (sign,rs,grter) es depth,nil))
					       else []
				| _ => []
		val randomlemmas = case prop of
				       "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => procDepth2nd (sign,rs,grter,[e]) (1,max) [e] depth) randlem)
						     else [])
				     | _  => []
		(* ランダム補題生成の補題の個数 *)
		val _ = if randlem = [] then print ""
			else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
		(* 証明された補題の表示 *)
		(*val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules randomlemmas))))
					 else print ""
			  | _ => print ""*)
				   
		val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
					 else print ""
			  | _ => print ""
	    in
		if n > max  then raise Stopped
		else
		    case prop of
			"Success" => (let
					 val _ = print "Lemmas:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
					 val _ = print "Proved:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsRules es0))
					 val _ = print "Success\n"
				     in
					 true
				     end )
		      | "Disproof" => ((print ("Disproof:" ^ (Trs.prEqs (MS.dropSortInMsRules es))));false)
		      | "Failed" => ((print "Failed\n");false)
		      | "Stopped" => if lemmas0 = [] then (print "We cannot find lemmas.\n"; raise Failure)
 				     else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		      | _ => false
				 
	    end handle Success => (print "Success\n"; true)
		     | Failure => (print "Failed\n"; false)
		     | Stopped => (print "Stopped\n"; false)
		     | Disproof => (print "Conjectures are non-Inductive Theorems\n"; false)
    in
	procSub (sign0,rs0,grter0,es0) 1 []
    end

(* ~Debug Version~ Default Version *)
fun procDepthPrintDef str depth = procDepthPrint str 6 depth

(* 補題の証明に補題を用いない(深さ入力) Main Process *)
fun procDepth_Nolemgen str max depth =
    let
	val (sign0,rs0,grter0,es0) = indPars str
					     
	fun procSub (sign,rs,grter,es) n lem =
	    let
		fun toleft (x,y) = x
		val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
		val prop = IndMs.ind (sign,rs,grter) es max
		val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nLemma Generation:" else print ""
		(* Difference MatchとNew Lemma Generationの手続き *)
		val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGen (sign,rs,grter) es,nil))
			     else []
		val soundlemmas = if prop = "Stopped" then L.filter (fn e => (IndMs.ind (sign,rs,grter) [e] max) = "Success") lemmas
				  else []
		(* 証明された補題の表示 *)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules soundlemmas)))
			  | _  => print ""
					
		val _ = case  prop  of
			    "Stopped" => if soundlemmas = [] then print "Random Lemma Generation:" else print ""
			  | _  => print ""
		(* Random Lemma Generationの手続き *)
		val randlem = case prop of
				  "Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDepth (sign,rs,grter) es depth,nil))
					       else []
				| _ => []
		val randomlemmas = case prop of
				       "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => (IndMs.ind (sign,rs,grter) [e] max) = "Success") randlem)
						     else [])
				     | _  => []
		(* ランダム補題生成の補題の個数 *)
		val _ = if randlem = [] then print ""
			else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
		(* 証明された補題の表示 *)
		(*val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules randomlemmas))))
					 else print ""
			  | _ => print ""*)
				   
		val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
					 else print ""
			  | _ => print ""
		(*val max = 6*)
	    in
		if n > max  then raise Stopped
		else
		    case prop of
			"Success" => (let
					 val _ = print "Lemmas:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
					 val _ = print "Proved:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsRules es0))
					 val _ = print "Success\n"
				     in
					 true
				     end )
		      | "Disproof" => ((print ("Disproof:" ^ (Trs.prEqs (MS.dropSortInMsRules es))));false)
		      | "Failed" => ((print "Failed\n");false)
		      | "Stopped" => if lemmas0 = [] then (print "We cannot find lemmas.\n"; raise Failure)
 				     else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		      | _ => false
				 
	    end handle Success => (print "Success\n"; true)
		     | Failure => (print "Failed\n"; false)
		     | Stopped => (print "Stopped\n"; false)
		     | Disproof => (print "Conjectures are non-Inductive Theorems\n"; false)
    in
	procSub (sign0,rs0,grter0,es0) 1 []
    end

(* 補題の証明に補題を用いない Main Process-Default *)
fun procDepth_NolemgenDef str depth = procDepth_Nolemgen str 6 depth

(* 補題の証明に補題を用いない ~Debug Version~ *)
fun procDepth_NolemgenPrint str max depth =
    let
	val (sign0,rs0,grter0,es0) = indPars str
					     
	fun procSub (sign,rs,grter,es) n lem =
	    let
		fun toleft (x,y) = x
		val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
		val prop = IndMs.ind (sign,rs,grter) es max 
		val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nLemma Generation:" else print ""
		(* Difference MatchとNew Lemma Generationの手続き *)
		val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGenPrint (sign,rs,grter) es,nil))
			     else []
		val soundlemmas = if prop = "Stopped" then L.filter (fn e => (IndMs.ind (sign,rs,grter) [e] max) = "Success") lemmas
				  else []
		(* 証明された補題の表示 *)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then print "\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules soundlemmas)))
			  | _  => print ""
					
		val _ = case  prop  of
			    "Stopped" => if soundlemmas = [] then print "Random Lemma Generation:" else print ""
			  | _  => print ""
		(* Random Lemma Generationの手続き *)
		val randlem = case prop of
				  "Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDepthPrint (sign,rs,grter) es depth,nil))
					       else []
				| _ => []
		val randomlemmas = case prop of
				       "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => (IndMs.ind (sign,rs,grter) [e] max) = "Success") randlem)
						     else [])
				     | _  => []
		(* ランダム補題生成の補題の個数 *)
		val _ = if randlem = [] then print ""
			else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
		(* 証明された補題の表示 *)
		(*val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("\nProved:" ^ (Trs.prEqs (MS.dropSortInMsRules randomlemmas))))
					 else print ""
			  | _ => print ""*)
				   
		val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
		val _ = case prop of
			    "Stopped" => if soundlemmas = [] then (if randomlemmas = [] then print " []\n" else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
					 else print ""
			  | _ => print ""
		(*val max = 6*)
	    in
		if n > max  then raise Stopped
		else
		    case prop of
			"Success" => (let
					 val _ = print "Lemmas:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
					 val _ = print "Proved:"
					 val _ = print (Trs.prEqs (MS.dropSortInMsRules es0))
					 val _ = print "Success\n"
				     in
					 true
				     end )
		      | "Disproof" => ((print ("Disproof:" ^ (Trs.prEqs (MS.dropSortInMsRules es))));false)
		      | "Failed" => ((print "Failed\n");false)
		      | "Stopped" => if lemmas0 = [] then (print "We cannot find lemmas.\n"; raise Failure)
 				     else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		      | _ => false
				 
	    end handle Success => (print "Success\n"; true)
		     | Failure => (print "Failed\n"; false)
		     | Stopped => (print "Stopped\n"; false)
		     | Disproof => (print "Conjectures are non-Inductive Theorems\n"; false)
    in
	procSub (sign0,rs0,grter0,es0) 1 []
    end

(* 補題の証明に補題を用いない(深さ入力) ~Debug Version~ Default*)
fun procDepth_NolemgenPrintDef str depth =  procDepth_NolemgenPrint str 6 depth

(* 補題のみ表示 (深さは補題の左辺)*)
fun procLemmas str =
  let
      val (sign0,rs0,grter0,es0) = indPars str
      val max = 6
		    
      fun procSub (sign,rs,grter,es) n lem =
	  let
	      fun toleft (x,y) = x
	      (*val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")*)
	      val prop = IndMs.ind (sign,rs,grter) es max 
	      (* Difference MatchとNew Lemma Generationの手続き *)
	      val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGen (sign,rs,grter) es,nil))
			   else []
	      val soundlemmas = if prop = "Stopped" then L.filter (fn e => (proc2nd (sign,rs,grter,[e]) (1,max) [e])) lemmas
				else []
					 
	      (* Random Lemma Generationの手続き *)
	      val randlem = case prop of
				"Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDef (sign,rs,grter) es,nil))
					     else []
			      | _ => []
	      val randomlemmas = case prop of
				     "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => proc2nd (sign,rs,grter,[e]) (1,max) [e]) randlem)
						   else [])
				   | _  => []
					       
	      val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
	  in
	      if n > max  then raise Stopped
	      else
		  case prop of
		      "Success" => (let
				       val _ = print "\nLemmas:"
				       val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
				   in
				       true
				   end)
		    | "Disproof" => (let
				       val _ = print "\nLemmas:"
				       val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
				   in
				       false
				   end )
		    | "Failed" => (let
				       val _ = print "\nLemmas:"
				       val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
				   in
				       false
				   end)
		    | "Stopped" => if lemmas0 = [] then (let
							    val _ = print "\nLemmas:"
							    val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
							 in raise Failure end)
 				   else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		    | _ => false
			       
	  end handle Success => true
		   | Failure => false
		   | Stopped => false
		   | Disproof => false		    
  in
      procSub (sign0,rs0,grter0,es0) 1 []
  end

(* 補題のみ表示 (深さは入力)*)      
fun procDepthLemmas str depth =
  let
      val (sign0,rs0,grter0,es0) = indPars str
      val max = 6
		    
      fun procSub (sign,rs,grter,es) n lem =
	  let
	      fun toleft (x,y) = x
	      (*val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")*)
	      val prop = IndMs.ind (sign,rs,grter) es max 
	      (* Difference MatchとNew Lemma Generationの手続き *)
	      val lemmas = if prop = "Stopped" then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.lemGen (sign,rs,grter) es,nil))
			   else []
	      val soundlemmas = if prop = "Stopped" then L.filter (fn e => procDepth2nd (sign,rs,grter,[e]) (1,max) [e] depth) lemmas
				else []
	      (* Random Lemma Generationの手続き *)
	      val randlem = case prop of
				"Stopped" => if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDepth (sign,rs,grter) es depth,nil))
					     else []
			      | _ => []
	      val randomlemmas = case prop of
				     "Stopped" => (if soundlemmas = [] then L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => procDepth2nd (sign,rs,grter,[e]) (1,max) [e] depth) randlem)
						   else [])
				   | _  => []       
	      val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas@randomlemmas,[]))),nil)
	  in
	      if n > max  then raise Stopped
	      else
		  case prop of
		      "Success" => (let
				       val _ = print "\nLemmas:"
				       val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
				   in
				       true
				   end)
		    | "Disproof" => (let
				       val _ = print "\nLemmas:"
				       val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
				   in
				       false
				   end )
		    | "Failed" => (let
				       val _ = print "\nLemmas:"
				       val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
				   in
				       false
				   end)
		    | "Stopped" => if lemmas0 = [] then (let
							    val _ = print "\nLemmas:"
							    val _ = print (Trs.prEqs (MS.dropSortInMsEqs lem))
							 in raise Failure end)
 				   else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
		    | _ => false
			       
	  end handle Success => true
		   | Failure => false
		   | Stopped => false
		   | Disproof => false		    
  in
      procSub (sign0,rs0,grter0,es0) 1 []
  end
								    
end (* of local *)

end (* of struct *)
    
