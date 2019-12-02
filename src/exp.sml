(* file: exp.sml *)
(* description: experiment file *)
(* author: Hiroto Kato *)

signature EXP = 
sig
    val main: string * string list -> OS.Process.status
end

structure Exp = 
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

val helpMsg = "experiment file "

(* no lemma generations version *)
fun exp1 str =
    let
        val (sign0,rs0,grter0,es0) = IndMain.indPars str
        val max = 6
        val _ = print ("********************************[Step " ^ (Int.toString 1) ^ "]********************************\n")
        val prop = IndMs.ind (sign0,rs0,grter0) es0 max
    in
        case prop of
            "Success" => (let
                             val _ = print "Proved:"
                             val _ = print (Trs.prEqs (MS.dropSortInMsRules es0))
                             val _ = print "Success\n"
                         in
                             true
                         end )
          | "Disproof" => ((print ("Disproof:" ^ (Trs.prEqs (MS.dropSortInMsRules es0))));false)
          | "Failed" => ((print "Failed\n");false)
          | "Stopped" => ((print "Stopped\n");false)
          | _ => false
    end handle Success => (print "Success\n"; true)
             | Failure => (print "Failed\n"; false)
             | Stopped => (print "Stopped\n"; false)
             | Disproof => (print "Disproof\n"; false)

(* only divergence critic *)
fun exp2 str =
    let
        val (sign0,rs0,grter0,es0) = IndMain.indPars str
        val max = 6
                      
        fun procSub (sign,rs,grter,es) n lem =
            let
                fun toleft (x,y) = x
                val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
                val prop = IndMs.ind (sign,rs,grter) es max 
                val _ = if prop = "Stopped"
                        then print "Rewriting induction diverges.\nLemma Generation:"
                        else print ""
                (* Difference Match Procedure *)
                val lemmas = if prop = "Stopped"
                             then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.DivCritic (sign,rs,grter) es,nil))
                             else []
                val soundlemmas = if prop = "Stopped"
                                  then L.filter (fn e => IndMain.proc2nd (sign,rs,grter,[e]) (1,max) [e]) lemmas
                                  else []
                val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas,[]))),nil)
                val _ = case prop of
                            "Stopped" => if soundlemmas = []
                                         then print " []\n"
                                         else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0)))
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

(* only lemma generation based on generalization and difference matching *)
fun exp3 str =
    let
        val (sign0,rs0,grter0,es0) = IndMain.indPars str
        val max = 6
                      
        fun procSub (sign,rs,grter,es) n lem =
            let
                fun toleft (x,y) = x
                val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
                val prop = IndMs.ind (sign,rs,grter) es max 
                val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nLemma Generation:" else print ""
                (* lemma generation based on generalization and difference matching procedure *)
                val lemmas = if prop = "Stopped"
                             then L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.DmNewLem (sign,rs,grter) es,nil))
                             else []
                val soundlemmas = if prop = "Stopped"
                                  then L.filter (fn e => IndMain.proc2nd (sign,rs,grter,[e]) (1,max) [e]) lemmas
                                  else []
             
                val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (soundlemmas,[]))),nil)
                val _ = case prop of
                            "Stopped" => if soundlemmas = []
                                         then print " []\n"
                                         else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0)))
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
        
(* only lemma generation based on random lemma generation of rhs *)
fun exp4 str =
    let
        val (sign0,rs0,grter0,es0) = IndMain.indPars str
        val max = 6

        fun procSub (sign,rs,grter,es) n lem =
            let
                fun toleft (x,y) = x
                val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
                val prop = IndMs.ind (sign,rs,grter) es max 
                val _ = if prop = "Stopped" then print "Rewriting induction diverges.\nRandom Lemma Generation:" else print ""
                (* Random Lemma Generation procedure *)
                val randlem = case prop of
                                  "Stopped" => L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDef (sign,rs,grter) es,nil))
                                | _ => []
                val randomlemmas = case prop of
                                       "Stopped" => L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => IndMain.proc2nd (sign,rs,grter,[e]) (1,max) [e]) randlem)
                                     | _  => []
                (* the number of lemmas of rondom lemma generation *)
                val _ = if randlem = [] then print ""
                        else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
             
                val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (randomlemmas,[]))),nil)
                val _ = case prop of
                            "Stopped" => (if randomlemmas = []
                                          then print " []\n"
                                          else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
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
                      | "Stopped" => if lemmas0 = []
                                     then (print "We cannot find lemmas.\n"; raise Failure)
                                     else procSub (sign,rs,grter,LU.union (es,lemmas0)) (n+1) (LU.union (lem@lemmas0,nil))
                      | _ => false
           
            end handle Success => (print "Success\n"; true)
                     | Failure => (print "Failed\n"; false)
                     | Stopped => (print "Stopped\n"; false)
                     | Disproof => (print "Conjectures are non-Inductive Theorems\n"; false)
    in
        procSub (sign0,rs0,grter0,es0) 1 []
    end
      
(* 右辺のランダム生成に基づく補題生成法(深さ入力)のみ *)
(* only lemma generation based on random lemma generation of rhs(input depth) *)        
fun exp5 str =
    let
        val (sign0,rs0,grter0,es0) = IndMain.indPars str
        val max = 6
        
        fun procSub (sign,rs,grter,es) n lem =
            let
                fun toleft (x,y) = x
                val _ = print ("********************************[Step " ^ (Int.toString n) ^ "]********************************\n")
                val prop = IndMs.ind (sign,rs,grter) es max 
                val _ = if prop = "Stopped"
                        then print "Rewriting induction diverges.\nRandom Lemma Generation:"
                        else print ""
                (* Random Lemma Generation procedure *)
                val randlem = case prop of
                                  "Stopped" => L.filter (fn ((l,r),ty) => not(l=r)) (MS.diffMsRules (LemGen.randLemGenDepth (sign,rs,grter) es 4,nil)) (* input depth*)
                                | _ => []
                val randomlemmas = case prop of
                                       "Stopped" => L.filter (fn ((l,r),ty) => not(l=r)) (L.filter (fn e => IndMain.proc2nd (sign,rs,grter,[e]) (1,max) [e]) randlem)
                                     | _  => []
                (* the number of lemmas of rondom lemma generation *)                                                 
                val _ = if randlem = []
                        then print ""
                        else print ("\nlemmas: "^(Int.toString (L.length (L.filter grter (MS.dropSortInMsRules randlem))))^"\n")
             
                val lemmas0 = LU.union (L.filter (fn ((l,r),ty) => not(l=r)) (toleft (IndMs.simplify (rs,grter) (randomlemmas,[]))),nil)
                val _ = case prop of
                            "Stopped" => (if randomlemmas = []
                                          then print " []\n"
                                          else print ("Proved:" ^ (Trs.prEqs (MS.dropSortInMsRules lemmas0))))
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

fun main (name, args) =
    if null args then (print helpMsg; OS.Process.success)
    else let val filename = L.hd args
             val _ = exp1 filename
         in OS.Process.success
         end

end 

end

(* 
CM.make "sources.cm";
SMLofNJ.exportFn ("exp", Exp.main);
sml @SMLload=exp.x86-linux 
*)
