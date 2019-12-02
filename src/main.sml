(* file: main.sml *)
(* description: Inductive theorem proving with lemma generation of many-sorted TRS in MSTRS format *)
(* author: Hiroto Kato *)

signature MAIN = 
sig
    val toolname: string
    val version: string
    val helpMsg: string
    val main: string * string list -> OS.Process.status
end

structure Main = 
struct

local 
    structure L = List
    structure LU = ListUtil
in

val toolname = "ind"
val version = "0.01"
val optionMsg = "[Option]\n" ^
                "-D     --debug      : print proof process.\n" ^
                "-d=INT --depth=INT  : when we conjecture lemmas by random generation of rhs of lemmas,\n" ^
                "                      we decide how much to make the depth of rhs of lemma.\n"^
                "                      The default is the depth of lhs of lemma.\n"^
                "-nI    --noIteration: when we prove lemmas, we don't use the lemma generation.\n"^
                "--lemma             : print lemmas.\n"
val helpMsg = 
    toolname ^ " v" ^ version ^ "\n"
    ^ "Usage: sml @SMLload=" ^ toolname ^ ".x86-linux filename [Option]\n"
    ^ optionMsg ^ "\n"
val option1 = ["--debug","-D","--noIteration","-nI","--lemma"]
val option2 = ["--depth=","-d="]
                  
fun main (name, args) =
    if null args then (print helpMsg; OS.Process.success)
    else if L.length args = 1 then (IndMain.procDef (L.hd args);OS.Process.success)
    else let val filename = L.hd args
             val rest = L.tl args
             val isTheorem =
                 if L.exists (fn str => LU.member str option1) rest
                    orelse L.exists (fn str => L.exists (fn pattern => String.isSubstring pattern str) option2) rest 
                 then case LU.member "--lemma" rest of 
                          false => (case LU.member "--debug" rest
                                         orelse LU.member "-D" rest of
                                        true => (case LU.member "--noIteration" rest
                                                      orelse LU.member "-nI" rest of
                                                     true => (case L.exists (fn str => String.isSubstring "--depth=" str) rest
                                                                   orelse L.exists (fn str => String.isSubstring "-d=" str) rest of
                                                                  true => (case Util.intStrL rest option2 of
                                                                               0 => IndMain.proc_NolemgenPrintDef filename
                                                                             | depth => IndMain.procDepth_NolemgenPrintDef filename depth)
                                                                | false => IndMain.proc_NolemgenPrintDef filename)
                                                   | false => (case L.exists (fn str => String.isSubstring "--depth=" str) rest
                                                                    orelse L.exists (fn str => String.isSubstring "-d=" str) rest of
                                                                   true => (case Util.intStrL rest option2 of
                                                                                0 => IndMain.procPrintDef filename
                                                                              | depth => IndMain.procDepthPrintDef filename depth)
                                                                 | false => IndMain.procPrintDef filename))
                                      | false => (case LU.member "--noIteration" rest
                                                       orelse LU.member "-nI" rest of
                                                      true => (case L.exists (fn str => String.isSubstring "--depth=" str) rest
                                                                    orelse L.exists (fn str => String.isSubstring "-d=" str) rest of
                                                                   true => (case Util.intStrL rest option2 of
                                                                                0 => IndMain.proc_NolemgenDef filename
                                                                              | depth => IndMain.procDepth_NolemgenDef filename depth)
                                                                 | false => IndMain.proc_NolemgenDef filename)
                                                    | false => (case L.exists (fn str => String.isSubstring "--depth=" str) rest
                                                                     orelse L.exists (fn str => String.isSubstring "-d=" str) rest of
                                                                    true => (case Util.intStrL rest option2 of
                                                                                 0 => IndMain.procDef filename
                                                                               | depth => IndMain.procDepthDef filename depth)
                                                                  | false => IndMain.procDef filename)))
                        | true => (case L.exists (fn str => String.isSubstring "--depth=" str) rest
                                        orelse L.exists (fn str => String.isSubstring "-d=" str) rest of
                                       true => (case Util.intStrL rest option2 of
                                                    0 => IndMain.procLemmas filename
                                                  | depth => IndMain.procDepthLemmas filename depth)
                                     | false => IndMain.procLemmas filename)
                                      
                 else (print ("Error: unrecognized option\n");false)
         in OS.Process.success
            handle Io => (print ("Error: failed to read the file " ^ filename ^ "\n");
                          OS.Process.success)
         end
             
end (* of local *)
end (* of struct *)

(* 
CM.make "sources.cm";
SMLofNJ.exportFn ("ind", Main.main);
sml @SMLload=ind.x86-linux 

Option
--debug: we display proof process.
--depth=INT: the default is the depth of lhs of lemma.
--noIteration: when we prove lemmas, we don't use the lemma generation.
--lemma: print lemmas
-- lemma -d=INT: print lemmas and the depth of lhs of lemma is INT
*)
