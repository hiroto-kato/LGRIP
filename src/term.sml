(* file: term.sml *)
(* description: first-order terms *)
(* author: Hiroto Kato *)

signature TERM = 
sig 
    type var_key = Var.key
    type fun_key = Fun.key
    datatype term = Var of var_key | Fun of fun_key * term list
    val root: term -> Symbol.symbol
    val args: term -> term list
    val isVar: term -> bool
    val isFun: term -> bool
    val vars: term -> var_key list
    val toSymbol: fun_key list -> Symbol.symbol list
    val toSymbolV: var_key list -> Symbol.symbol list
    val funs: term -> fun_key list
    val nonrec: term -> bool
    val toString: term -> string
    val fromString: string -> term
    val toStringInTerms: term list -> string
    val cropId: string -> string * string
    val cropTerm: string -> term * string
    val cropKeySeparatedTermPair: string -> string -> (term * term) * string
    val readKeySeparatedTermPair: string -> string -> (term * term)
                                                          
    (* position *)
    type position = int list
    exception PositionNotInTerm 
    val prPos: position -> string
    val pos: term -> position list 
    val symbol: term -> position -> Symbol.symbol
    val subterm: term -> position -> term 

    (* context *)
    type context = term -> term 
    val makeContext: term -> position -> context
    val fillContext: context -> term -> term

    val dfun: term -> fun_key option
    val isGround: term -> bool
    val isConstructor: fun_key list -> term -> bool
    val isBasic: fun_key list * fun_key list -> term -> bool
    val findBasicSubtermLiOc: fun_key list * fun_key list -> term -> (context * term) option 
    val termMatchpos: term -> term -> position list
    val termMatchPosition: term -> term -> position
    val isHierarchy: fun_key list * fun_key list -> term -> bool (* 階層項 *)

    val isLinear: term -> bool
    val isDfunInRoot: fun_key list -> term -> bool
end

structure Term : TERM =
struct
local 
    structure L = List
    structure LP = ListPair
    structure LU = ListUtil
    structure SU = StringUtil 
in

type var_key = Var.key
type fun_key = Fun.key
datatype term = Var of var_key | Fun of fun_key * term list

(* 項が変数かどうか *)
fun isVar (Var t) = true
  | isVar (Fun t) = false
                        
(* 項が変数でないかどうか *)
fun isFun (Fun t) = true
  | isFun (Var t) = false
                        
(* 与えられた項の引数を返す *)
fun args (Var t) = []
  | args (Fun (f,ts)) = ts
                            
(* 根記号を返す *)
fun root (Var t) = Symbol.V t   
  | root (Fun (f,ts)) = Symbol.F f
                                 
(* tからV(t)を返す *)
fun vars (Var x) = [x]
  | vars (Fun (f,ts)) = vars_a ts
and vars_a nil = nil
  | vars_a (t::ts) = ListUtil.union ((vars t), (vars_a ts))
                                    
(* 関数記号集合をsymbolにする関数 *)
fun toSymbol nil = nil
  | toSymbol (f::fs) = (Symbol.F f)::(toSymbol fs)

(* 変数集合をsymbolにする関数 *)
fun toSymbolV nil = nil
  | toSymbolV (v::vs) = (Symbol.V v)::(toSymbolV vs)
                                          
(* 関数記号の集合 *)
fun funs (Var x) = nil
  | funs (Fun (f,ts)) = ListUtil.union ([f]@(funs_a ts),nil)
and funs_a nil = nil
  | funs_a (t::ts) = ListUtil.union ((funs t)@(funs_a ts),nil)
                                    
(* ゼロ引数の関数(non-recursive)かどうか *)
fun nonrec (Var x) = false
  | nonrec (Fun (f,ts)) = if ts=nil then true
                          else false
                                   
fun toString (Var x) =  "?" ^ (Var.toString x)
  | toString (Fun (f,[])) = (Fun.toString f)
  | toString (Fun (f,ts)) = (Fun.toString f) ^ "(" ^ (toStringList ts)
and toStringList [] = "" (* does not reach here *)
  | toStringList ([t]) = (toString t) ^ ")"
  | toStringList (t::ts) = (toString t) ^ "," ^ (toStringList ts)
                                                    
fun toStringInTerms nil = "\t[  ]\n\n"
  | toStringInTerms l =
    let
        fun terms (t::nil) = "\t  " ^ (toString t)
          | terms (t::ts)  = "\t  " ^ (toString t) ^ "\n" ^ (terms ts)
        fun termsf (t::nil) = (toString  t)
          | termsf (t::ts) = (toString  t) ^ "\n" ^ (terms ts)
    in
        "\t[ " ^ (termsf l) ^ " ]\n\n"
    end
        

structure TermSpecialSymbols = struct val special = [#"(", #")", #","]  end
structure TermLex = Lexical (TermSpecialSymbols);
structure TermParsing = Parsing (TermLex);

local

    fun makeFun (id, ts) = (case Symbol.fromString id of
                                Symbol.F f => Fun (f, ts)
                              | Symbol.V _ => raise Fail "Syntax error: function symbol expected")
    fun makeList (t, ts) = t::ts
    fun makeList1 t = t::nil
    fun makeAtom id  = (case Symbol.fromString id of
                            Symbol.F c => Fun (c, []) 
                          | Symbol.V x => Var x)

    open TermParsing
    infix 6 $--
    infix 5 --
    infix 3 >>
    infix 0 ||

    fun term toks =
        ( id --  "(" $-- termlist >> makeFun || atom ) toks
    and termlist toks =
        ( termseq -- $ ")" >> #1 ) toks
    and termseq toks =
        ( term -- "," $-- termseq >> makeList || term >> makeList1 ) toks
    and atom toks  =
        ( id >> makeAtom ) toks
in 
fun fromString str = reader term str
end (* of local *)

fun cropId str = TermLex.cropId str

fun cropTerm str = let val (id, body) = cropId str
                       val (init, rest) = SU.scanBalancedPar body
                       val t = fromString (id ^ init)
                   in (t, rest) end

fun cropKeySeparatedTermPair key str 
    = let val (lhs, str1)  = cropTerm str
      in case SU.scanKey key str1 of 
             SOME str2 => let val (rhs, rest) = cropTerm str2
                          in ((lhs,rhs), rest) end
           | NONE => raise Fail ("Syntax error: unexpected " ^ "key")
      end

fun readKeySeparatedTermPair key str = SU.readWith (cropKeySeparatedTermPair key) str


type position = int list
exception PositionNotInTerm 

(* 位置を文字列に変換する *)
fun prPos nil = "{}"
  | prPos (t::nil) = (Int.toString t) ^ "}"
  | prPos (t::ts) = if t=0 then "{" ^ (Int.toString t) ^ "," ^ (prPos ts)
                    else (Int.toString t) ^ "," ^ (prPos ts)
(* 項の位置のリストを返す *)
fun pos t = 
    let
        (* posList :  引数 => (Term list,list) 返り値 => int list list *)
        fun posList ((Var x)::nil) l = l::nil
          (* [l] @ (postList ls (lの最後の要素を削除し、lの最後の要素+1を追加したリスト)) *)
          | posList ((Var x)::ls) l = [l]@(posList ls (L.rev (L.drop((L.rev l),(L.last l)))@[(L.last l)+1]))
          | posList ((Fun (f,nil))::nil) l = l::nil
          | posList ((Fun (f,nil))::ls) l = [l]@(posList ls (L.rev (L.drop((L.rev l),(L.last l)))@[(L.last l)+1]))
          | posList ((Fun (f,ts))::nil) l = if (L.last l)=1
                                            then [l]@(posList ts (l@[1]))
                                            else [l]@(posList ts (l@[(L.last l)-1]))
          | posList ((Fun (f,ts))::ls) l = if (L.hd l)=1
                                           then [l]@(posList ts (l@[1]))@(posList ls (L.rev (L.drop((L.rev l),(L.last l)))@[(L.last l)+1]))
                                           else [l]@(posList ts (l@[1]))@(posList ls ((L.rev (L.drop((L.rev l),(L.last l))))@[(L.last l)+1]))

        (* position : 引数 => (Term,list) , 返り値 => int list list *)     
        fun position (Var x) l = [[]]
          | position (Fun (f,nil)) l = [[]]
          | position (Fun (f,ts)) l = []::(posList ts l)
                                              
    in 
        position t [1] 
    end 
        

(* t(p)を返す *)
fun symbol (Var x) l = if l=nil
                       then Symbol.V x
                       else raise PositionNotInTerm
  | symbol (Fun (f,ts)) nil = Symbol.F f
  | symbol (Fun (f,(t::ts))) (l::ls) = case l of 
                                           1 => symbol t ls
                                         | 0 => raise PositionNotInTerm
                                         | _ => symbolList ts ([l-1]@ls)
and symbolList (t::nil) (l::ls) = symbol t ls
  | symbolList (t::ts) (l::ls) = if l=1
                                 then symbol t ls
                                 else symbolList ts ([l-1]@ls)

(* t|pを返す *)
fun subterm (Var x) l = if l=nil
                        then Var x
                        else raise PositionNotInTerm
  | subterm (Fun t) nil = Fun t
  | subterm (Fun (f,(t::ts))) (l::ls) = case l of 
                                            1 => subterm t ls
                                          | 0 => raise PositionNotInTerm
                                          | _ => if ts=nil
                                                 then subterm t ([l-1]@ls)
                                                 else subtermList ts ([l-1]@ls)
and subtermList (t::nil) (l::ls) = subterm t ls
  | subtermList (t::ts) (l::ls) = if l=1
                                  then subterm t ls
                                  else subtermList ts ([l-1]@ls)
  | subtermList _ _ = raise PositionNotInTerm  
                            
type context = term -> term

(* 文脈を返す関数 *)
fun makeContext (Var x) nil tc = tc
  | makeContext (Var x) p tc = raise PositionNotInTerm
  | makeContext (Fun (f,ts)) nil tc = tc
  | makeContext (Fun (f,(t::ts))) (p::ps) tc = if p=1
                                               then Fun (f,(makeContext t ps tc)::ts)
                                               else Fun (f,t::(makeContextL ts ([p-1]@ps) tc)::nil)
  | makeContext _ _ tc = raise PositionNotInTerm          
and makeContextL (t::ts) (p::ps) tc = if p=1
                                      then makeContext t ps tc
                                      else makeContextL ts ([p-1]@ps) tc
  | makeContextL _ _ tc = raise PositionNotInTerm

fun fillContext c t = c t;

(* 定義記号のoptionを返す *)
fun dfun  (Fun (f,ts)) = SOME f
  | dfun (Var x) = NONE

(* 項が基底項かを判定する関数 *)
fun isGround term = (vars term = nil)
                        
(* 項が構成子項かを判定する関数 *)
fun isConstructor cfuns term =
    let
        val tfuns = LU.union ((funs term),[])
    in
        if tfuns = nil
        then true 
        else (if (L.filter (fn x => not(LU.member x cfuns)) tfuns) = nil
              then true
              else false)
    end
        
(* 項が基本項か判定する関数 *)
fun isBasic (dfuns, cfuns) term = if isFun term
                                  then (LU.member (valOf(dfun term)) dfuns) andalso (L.all (fn t => isConstructor cfuns t) (args term))
                                  else false

(* 項が階層項か判定する関数 *)
fun isHierarchy (dfuns, cfuns) term = if isBasic (dfuns,cfuns) term
                                      then true
                                      else
                                          case dfun term of
                                              SOME x => (LU.member x dfuns) andalso (L.exists (fn t => isHierarchy (dfuns,cfuns) t) (args term))
                                            | NONE => false
                                                          
(* 基本部分項の最左最内出現を返す関数*)
fun findBasicSubtermLiOc (dfuns, cfuns) term =
    let
        val tpos = pos term (* term position List *) 
        val subtl = L.map (fn p => ((subterm term p),p)) tpos (* (subterm * position) List *)
        val bsubtl = L.filter (fn (t,p) => (isBasic (dfuns, cfuns) t)) subtl (* (basic subterm * position) List *)
        (* 最左最内出現 *)
        fun lipos nil nil = nil
          | lipos [(t0,p0)] [] = [(t0,p0)]
          | lipos [] ((t1,p1)::tps) = lipos [(t1,p1)] tps
          | lipos [(t0,p0)] ((t1,p1)::tps) = if (L.length p0) > (L.length p1)
                                             then lipos [(t0,p0)] tps
                                             else lipos [(t1,p1)] tps
        fun cu nil = NONE
          | cu [(t,p)] = case [(t,p)] = nil of
                             true => NONE
                           | false => SOME ((makeContext term p), t)
    in
        cu (lipos nil bsubtl)
    end
        
(* term1とterm2 term1 > term2)のmatchするpositionを見つける *)
fun termMatchpos term1 term2 =
    let
        val tpos1 = pos term1
        val subtl = L.map (fn p => ((subterm term1 p),p)) tpos1
        val tpos2 = L.filter (fn (t,p) => (t = term2)) subtl
    in
        if tpos2=nil
        then nil
        else (L.map (fn (t,p) => p) tpos2)
    end
        
fun termMatchPosition term1 term2 =
    let
        val tpos1 = pos term1
        val subtl = L.map (fn p => ((subterm term1 p),p)) tpos1
        val tpos2 = L.filter (fn (t,p) => (t = term2)) subtl
    in
        if tpos2=nil
        then nil
        else L.hd (L.map (fn (t,p) => p) tpos2)
    end

fun isLinear term =
    let
        fun varsr (Var x) = [x]
          | varsr (Fun (f,ts)) = vars_a ts
        and vars_a nil = nil
          | vars_a (t::ts) = (varsr t)@(vars_a ts)
        fun TorF nil = true
          | TorF (t::ts) = if LU.member t ts
                           then false
                           else TorF ts
    in
        TorF (varsr term)
    end

fun isDfunInRoot dfuns term = if isVar term
                              then false 
                              else LU.member (root term) (toSymbol dfuns)
                                             
end (* of local *)         
end
