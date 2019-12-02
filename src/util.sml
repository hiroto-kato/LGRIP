(* file: util.sml *)
(* description: utility functions *)
(* author: Hiroto Kato *)
signature UTIL = 
sig
    val intStr : string -> int
    val intStrL : string list -> string list -> int
end

structure Util : UTIL =
struct

local
    structure L = List
    structure S = String
in

(* "*=INT" => INT *)
fun intStr str = case Int.fromString (S.str (L.last (S.explode str))) of
                     SOME i => i
                   | NONE => 0
(* find "*=INT" string from string list *)
fun intStrL strl strpattern = case L.find (fn s => L.exists (fn s1 => String.isSubstring s1 s) strpattern) strl of
                                  SOME str1 => intStr str1
                               |  NONE => 0
                                              
end (* of local *)

end (* of struct *)
