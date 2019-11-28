(* file: comp.sml *)
(* description: completion *)
(* author: Hiroto Kato *)

signature COMP = 
sig 
    type eqs = (Term.term * Term.term) list
    type rule = Term.term * Term.term
    type rules = (Term.term * Term.term) list
    val simplify: eqs * rules -> eqs * rules
    val delete: eqs * rules -> eqs * rules
    val orient: (Term.term * Term.term -> bool) -> eqs * rules -> eqs * rule * rules
    val compose: eqs * rule * rules -> eqs * rule * rules 
    val deduce: eqs * rule * rules -> eqs * rule * rules 
    val collapse: eqs * rule * rules -> eqs * rule * rules
    val prStatus: eqs * rule * rules -> eqs * rule * rules
    val pr: string -> eqs * rules -> eqs * rules
    val kbstep: (Term.term * Term.term -> bool) -> (eqs * rules) -> (eqs * rules)
    val kb: (Term.term * Term.term -> bool) -> eqs -> bool
end

structure Comp: COMP =
struct 

local 
    structure L = List
    structure AL = AssocList
    structure LP = ListPair
    structure LU = ListUtil
    structure T = Term
    structure S = Symbol
    structure SU = StringUtil
in

type eqs = (Term.term * Term.term) list
type rule = Term.term * Term.term
type rules = (Term.term * Term.term) list

exception Failure
exception Success of rules

fun simplify (es,rs) = ((L.map (fn (x,y) => ((Rewrite.linf rs x),(Rewrite.linf rs y))) es),rs)
fun delete (es,rs) = ((L.filter (fn (x,y) => not(x=y)) es),rs)
fun orient grter (es,rs) = 
    let 
	fun size (l,r) = L.length (Term.pos l) + L.length (Term.pos r)
	fun check (l,r) = if grter (l,r) then SOME (l,r) 
			  else if grter (r,l) then SOME (r,l) 
			  else NONE 
	fun select nil = NONE
	  | select (x::nil) = check x 
	  | select (x::xs) = case select xs of SOME y => if size x > size y then SOME y else case check x of SOME a => SOME a | NONE => SOME y

	fun del (l,lr)= L.filter (fn (x,y) => not((x,y)=lr orelse (y,x)=lr)) l
	
    in
	
	case select es of NONE => raise Failure
			 |SOME e =>((del (es,e)),e,rs)

    end
fun compose (es,rule,rs) = (es,rule,(L.map (fn (x,y) => (x,(Rewrite.linf (rs@[rule]) y))) rs))
fun deduce (es,rule,rs) = 
    let 
	val cpRlr1 = (L.concat (L.map (fn lr => (L.map (fn (x,y,z) => (x,z))
						       (let  
							    val (l,r) = Trs.rename (lr,rule)
							in
							    Cr.cpkRule false l r
						       end))) rs))

	val cpRlr2 = (L.concat (L.map (fn lr => (L.map (fn (x,y,z) => (x,z))
						       (let  
							    val (l,r) = Trs.rename (lr,rule)
							in
							    Cr.cpkRule false r l
						       end))) rs))

	val cplr = L.map (fn (x,y,z) => (x,z)) (let
						   val (l,r) = Trs.rename (rule,rule)
					       in 
						   Cr.cpkRule true rule rule
					       end)

	val cp1 = LU.union ((LU.union (cpRlr1,cpRlr2)),cplr)
    in
	(LU.union (es,cp1),rule,rs)
    end
fun collapse (es,rule,rs) = 
    let 
	val (xs,ys) = L.partition (fn (x,y) => Rewrite.isNF [rule] x) rs
	val nf = L.map (fn (x,y) => ((Rewrite.linf [rule] x),y)) ys
    in
	(LU.union (es,nf),rule,xs)
    end

(* 完備化の進行状況の表示 *)
fun prStatus (es, rule, rs) =
    let val _ = print (Trs.prEqs (rule::es))
	val _ = print (Trs.prRules rs)
    in (es, rule, rs) end

fun pr str (es,rs) =
  let val _ = print str
      val _ = print "ES"
      val _ = print (Trs.prEqs es)
      val _ = print "\nHS"
      val _ = print (Trs.prRules rs)
  in (es, rs) end
      
(* 完備化の帰納ステップ *)
fun kbstep grter (es,rs) =
     ((fn (es,rule,rs) => (es, rule::rs))
(*      o (fn (es,rule,rs) => (print "collapse\n";prStatus (es,rule,rs)))*)
      o collapse
      o (fn (es,rule,rs) => (print "deduce\n";prStatus (es,rule,rs)))
      o deduce
(*      o (fn (es,rule,rs) => (print "compose\n";prStatus (es,rule,rs)))*)
      o compose
      o (fn (es,rule,rs) => (prStatus (es,rule,rs)))
      o (orient grter)
      o (fn (es,rs) => if null es then raise (Success rs) else (es,rs))
(*      o (fn (es,rs) => pr "delete\n" (es, rs))*)
      o delete
(*      o (fn (es,rs) => pr "\n\nsimplify\n" (es, rs))*)
      o simplify) (es,rs)

fun kb grter es = 
    let
	fun main (es,rs) n = 
	    let 
		val i = Int.toString n
		val _ = print ("Step " ^ i ^ "\n")
	    in 
		main (kbstep grter (es,rs)) (n+1)
	    end
	fun suc rs = 
	    let 
		val _ = print "Success\n"
		val _ = print (Trs.prRules rs)
	    in
		true
	    end
    in
	main (es,nil) 1 handle (Success rs) => (suc rs)
    end 

end (* of local *)
end (* of struct *)

(*
実行例
(1)
val es = List.map Trs.rdEq ["W(?x) = S(W(?x))", "W(B(?x)) = S(?x)"];
val grter = PathOrder.lpoGt (PathOrder.rdPrec [("W",3),("S",2),("B",1)]);
Comp.kb grter es;

(2)
val es = List.map Trs.rdEq ["+(0,?x) = ?x", "+(-(?x),?x) = 0","+(+(?x,?y),?z) = +(?x,+(?y,?z))"];
val grter = PathOrder.lpoGt (PathOrder.rdPrec [("-",3),("+",2),("0",1)]);
Comp.kb grter es;
*)
