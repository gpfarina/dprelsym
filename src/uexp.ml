open Ast
open Mem
open Utils

let rec ueval: type a. mem -> a uexp  -> bool path_condition -> (ucodel * bool path_condition) =
  fun m-> fun e -> fun pc -> match e,pc with
  | Value(Bool(b)), _-> Uc(MBool(b)), pc
  | Value(Float(f)), _-> Uc(MFloat(f)), pc
  | Value(SymF(x)), _ -> Uc(MSymF(x)), pc
  | Value(SymB(x)), _ -> Uc(MSymB(x)), pc
  | Var(x),_ -> begin try lookup m x,pc with Not_found -> failwith (Printf.sprintf "Variable %s not defined" x) end
  | Neg(ne), pc ->
    begin
      let (v, pc')=ueval m ne pc in
      match v with
      | Uc(MBool(b)) -> Uc(MBool(not b)), pc'
      | Uc(MSymB(x)) -> let y=gen_fresh_sym () in
        Uc(MSymB(y)), (Pc(Neg(Eqb(CSymB(y), CSymB(x)))))::pc'
      | _ -> failwith "It should not happen ->2"
    end
  | Op(e1, op, e2), pc->
    let (v1, pc1)=ueval m e1 pc in
    let (v2, pc2)=ueval m e2 pc1 in
    match (v1, v2) with
    | Uc(MFloat(f1)), Uc(MFloat(f2)) -> Uc(MFloat(f1+. f2)), pc2
    | Uc(MSymF(x)), Uc(MFloat(f))      -> let y=gen_fresh_sym () in
      Uc(MSymF(y)) ,  (Pc(Eqf(CSymF(y), COp(CSymF(x), op, CFloat(f)))))::pc2
    | Uc(MFloat(f)), Uc(MSymF(x))      -> let y=gen_fresh_sym () in
      Uc(MSymF(y)) ,  (Pc(Eqf(CSymF(y), COp(CSymF(x), op, CFloat(f)))))::pc2
    | Uc(MSymF(x)), Uc(MSymF(y)) -> let z=gen_fresh_sym () in
      Uc(MSymF(z)) ,  (Pc(Eqf(CSymF(z), COp(CSymF(x), op, CSymF(y)))))::pc2
    | _ -> failwith "It should not happen -> 3"





