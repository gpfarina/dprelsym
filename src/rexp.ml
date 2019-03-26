open Ast
open Mem
open Utils
open Uexp
    
let rec reval: type a. rmem -> a rexp  -> bool path_condition -> (rcodel * bool path_condition) = fun m-> fun e -> fun pc ->
  let (v1, pc1)=ueval (proj_mem_l m) (eproj_l e) pc in
  let (v2, pc2)=ueval (proj_mem_r m) (eproj_r e) pc1 in
  match (v1, v2) with
  | Uc(MBool(true)), Uc(MBool(true)) -> (Rc(U(MBool(true))), pc2)
  | Uc(MBool(false)), Uc(MBool(false)) -> (Rc(U(MBool(false))), pc2)
  | Uc(MBool(true)), Uc(MBool(false)) -> (Rc(P(MBool(true), MBool(false))), pc2)
  | Uc(MBool(false)), Uc(MBool(true)) -> (Rc(P(MBool(false), MBool(true))), pc2)
  | Uc(MFloat(f1)), Uc(MFloat(f2)) -> if f1=f2 then(Rc(U(MFloat(f1))), pc2) else  (Rc(P(MFloat(f1), MFloat(f2))), pc2)
  | Uc(MSymF(x)), Uc(MSymF(y)) -> if x=y then(Rc(U(MSymF(x))), pc2) else  (Rc(P(MSymF(x), MSymF(y))), pc2)
  | Uc(MSymB(x)), Uc(MSymB(y)) -> if x=y then(Rc(U(MSymB(x))), pc2) else  (Rc(P(MSymB(x), MSymB(y))), pc2)
  | Uc(MFloat(f)), Uc(MSymF(y)) -> (Rc(P(MFloat(f), MSymF(y))), pc2)
  | Uc(MSymF(y)), Uc(MFloat(f)) -> (Rc(P(MSymF(y), MFloat(f))), pc2)
  | Uc(MBool(b)), Uc(MSymB(y)) -> (Rc(P(MBool(b), MSymB(y))), pc2)
  | Uc(MSymB(y)), Uc(MBool(b)) -> (Rc(P(MSymB(y), MBool(b))), pc2)
  | _->failwith "It should not happen --> reval 3"
