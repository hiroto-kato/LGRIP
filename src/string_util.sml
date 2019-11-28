(* file: string_util.sml *)
(* description: utility functions for string *)
(* author: Hiroto Kato *)

signature STRING_UTIL  = 
sig 
    val scanBalancedPar: string -> string * string
    val scanKey: string -> string -> string option
    val endWith: 'a -> string -> 'a 
    val readWith: (string -> 'a * string) -> string -> 'a 
end

structure StringUtil: STRING_UTIL =
struct

(* 開き括弧と閉じ括弧がバランスするところまでと，それ以降に分割する *)
(* ただし，最初の開き括弧までの間は，空白文字であればスキップする *)
fun scanBalancedPar str = 
    let fun rest 0 (body,ss) = SOME (body,ss)
	  | rest depth (body,ss) =
	    case Substring.getc ss of
		NONE => NONE
	      | SOME (#"(", ss1) => rest (depth+1) (body ^ "(", ss1)
	      | SOME (#")", ss1) => rest (depth-1) (body ^ ")", ss1)
	      | SOME (c, ss1) => rest depth (body ^ (String.str c), ss1)
	fun start (body,ss) = 
	    case Substring.getc ss of
		SOME (#"(", ss1) => rest 1 (body ^ "(", ss1)
	      | _ => SOME (body,ss)
    in case start ("", Substring.dropl (not o Char.isGraph) (Substring.full str)) of
	   NONE => raise Fail "Syntax error: unexpected \")\""
	 | SOME (body,rest) => (body,Substring.string rest)
    end

(* 先頭に key があれば，読みとばす *)
fun scanKey key str = 
    let val ss = Substring.dropl (not o Char.isGraph) (Substring.full str)
    in if Substring.isPrefix key ss
       then SOME (Substring.string (Substring.triml (String.size key) ss))
       else NONE 
    end

(* strを読みとばせれば ans で終了 *)
fun endWith ans str = 
    let val rest = valOf (scanKey "" str)
    in if rest = ""
       then ans
       else raise Fail ("Syntax error: unexpected string " ^ rest)
    end

(* cropfun で読んだ残りを読みとばせれば，切り出した解で終了 *)
fun readWith cropfun str = 
    let val (ans, rest) = cropfun str
    in endWith ans rest
    end

end


