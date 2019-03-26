type op =Add | Sub

type _ value =
  | Bool : bool -> bool value
  | Float : float -> float value
  | SymF : string -> 'a value
  | SymB : string -> 'a value

type _ uexp =
  | Value: 'a value -> 'a uexp
  | Var: string -> 'a uexp
  | Neg: bool uexp -> bool uexp
  | Op: float uexp * op * float uexp -> float uexp

type 'a cstre=
    True: bool cstre
  | CBool: bool -> bool cstre
  | CFloat: float -> float cstre
  | CSymB: string -> bool cstre
  | CSymF: string ->  float cstre 
  | COp: float cstre * op * float cstre -> float cstre
  | CLog: float cstre -> float cstre
  | CMax: float cstre * float cstre  -> float cstre
  | CFrac: float cstre * float cstre -> float cstre

type 'a cstr=
  | Assert: 'a cstre -> 'a cstr
  | Eqf: float cstre * float cstre ->   bool cstr
  | Eqb: bool cstre * bool cstre ->   bool cstr
  | Leq: float cstre * float cstre ->  bool cstr
  | Neg: bool cstr -> bool cstr


type 'a condition= Pc:'a cstr -> 'a condition
type 'a path_condition= 'a condition list

type _ rexp =
  | RValue: 'a value -> 'a rexp
  | RVar: string -> 'a rexp
  | RNeg: bool rexp -> bool rexp
  | ROp: float rexp * op * float rexp -> float rexp
  | RPair: 'a uexp * 'a uexp -> 'a rexp

type ucmd =
    USkip :  ucmd
  | UAss: string * 'a uexp ->  ucmd
  | USeq:  ucmd *  ucmd ->  ucmd

type cmd=
    Skip: cmd
  | Ass: string * 'a rexp -> cmd
  | RndAss: string * float rexp -> cmd
  | Ite: bool rexp * cmd *  cmd ->  cmd
  | Seq: cmd *  cmd -> cmd
  | Pair: ucmd *  ucmd ->  cmd


let rec eproj_l : type a. a rexp  -> a uexp = function
  | RValue(Bool(b)) -> Value(Bool(b))
  | RValue(Float(f)) -> Value(Float(f))
  | RValue(SymF(x)) -> Value(SymF(x))
  | RValue(SymB(x)) -> Value(SymB(x))
  | RVar(x)-> Var(x)
  | ROp(e1, op, e2) -> Op(eproj_l e1, op, eproj_l e2)
  | RNeg(e) -> Neg(eproj_l e)
  | RPair(el, _) -> el

let rec eproj_r : type a. a rexp  -> a uexp = function
  | RValue(Bool(b)) -> Value(Bool(b))
  | RValue(Float(f)) -> Value(Float(f))
  | RValue(SymF(x)) -> Value(SymF(x))
  | RValue(SymB(x)) -> Value(SymB(x))
  | RVar(x)-> Var(x)
  | ROp(e1, op, e2) -> Op(eproj_r e1, op, eproj_r e2)
  | RNeg(e) -> Neg(eproj_r e)
  | RPair(_, er) -> er


let rec cproj_l : cmd  ->  ucmd = function
  | Pair(cl, _)-> cl
  | Skip-> USkip
  | Ass(x,e1) -> UAss(x, eproj_l e1 )
  | Seq(c1, c2)-> USeq(cproj_l c1, cproj_l c2)
  | _ -> failwith "it should not happen- > 1"

let rec cproj_r : cmd  ->  ucmd = function
  | Pair(_, cr)-> cr
  | Skip-> USkip
  | Ass(x,e1) -> UAss(x, eproj_r e1 )
  | Seq(c1, c2)-> USeq(cproj_r c1, cproj_r c2)
  | _ -> failwith "it should not happen- > 1"
