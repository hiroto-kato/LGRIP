
(* file: list_util.sml *)
(* description: utility functions for list *)
(* author: Hiroto Kato *)

signature LIST_UTIL = 
sig 
    val member: ''a  -> ''a list -> bool
    val add: ''a  -> ''a list -> ''a list
    val union: ''a list * ''a list -> ''a list
    val intersection: ''a list * ''a list -> ''a list
    val mapAppend: ('a -> 'b list) -> 'a list -> 'b list
    val diff: ''a list * ''a list -> ''a list
    val toStringComma: ('a -> string) -> 'a list -> string
    val sequence: 'a list -> int -> 'a list list -> 'a list list
end

structure ListUtil : LIST_UTIL =
struct

local
    structure L = List
in

fun member x ys = L.exists (fn y => x = y) ys 
							
(* 集合としての演算 *)
fun add x ys = if member x ys then ys else x::ys

(* union (_,nil)だと順番も保持される *)
fun union ([], ys) = L.rev ys
  | union (x::xs,ys) = if member x ys then union (xs, ys)
      	    	       else union (xs, add x ys)
fun intersection (xs,ys) = L.filter (fn x => member x ys) xs

fun mapAppend f [] = []
  | mapAppend f (x::xs) = (f x) @ (mapAppend f xs)

(* xsからysを取り除く *)				      
fun diff (xs,ys) = L.filter (fn x => not(member x ys)) xs

fun toStringComma f (str::nil) = f str
  | toStringComma f (str::strl) = (f str) ^ "," ^ (toStringComma f strl)

(* 重複順列 *)
fun sequence [] _ _ = []
  | sequence xs 0 ys = ys
  | sequence xs n [] = sequence xs (n-1) (L.map (fn x => [x]) xs)
  | sequence xs n ys = sequence xs (n-1) (L.concat (L.map (fn x => L.map (fn y => y@[x]) ys) xs))

	
end (*of local*)

end (*of struct*)
