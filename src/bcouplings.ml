open Mem
open Ast
open Utils
open Rexp

let uval_to_cstr v=
  match v with
  | Rc(U(MFloat(f))) -> CFloat(f)
  | Rc(U(MSymF(s))) -> CSymF(s)
  | _ -> failwith "epsilon should be either symbolic or float and unary"
           
let bern_eq m1 x theta ex pc=
  let x1=gen_fresh_sym() in
  let x2=gen_fresh_sym () in
  let eps=gen_fresh_sym () in
  let v=lookup m1 "epsilon_c" in
  let m=remove m1 "epsilon_c" in
  match theta with
  | Rc(U(MFloat(_))) ->
    ("epsilon_c", Rc(U(MSymF(eps))))::((x, Rc(P(MSymB(x1), MSymB(x2))))::m), Skip,
    ex, Pc(Eqf(CSymF(eps), COp(uval_to_cstr v, Add, CFloat(0.0))))::Pc(Eqb(CSymB(x1), CSymB(x2)))::pc
  | Rc(U(MSymF(_))) ->
    ("epsilon_c", Rc(U(MSymF(eps))))::((x, Rc(P(MSymB(x1), MSymB(x2))))::m), Skip,
    ex, Pc(Eqf(CSymF(eps), COp(uval_to_cstr v, Add, CFloat(0.0))))::Pc(Eqb(CSymB(x1), CSymB(x2)))::pc                            
  | Rc(P(MFloat(f1), MFloat(f2))) ->
      ("epsilon_c", Rc(U(MSymF(eps))))::((x, Rc(P(MSymB(x1), MSymB(x2))))::m), Skip,
      ex, Pc(Eqf(CSymF(eps), COp(uval_to_cstr v, Add,
                                 CMax(CLog(CFrac(uval_to_cstr (Rc(U(MFloat f1))),uval_to_cstr (Rc(U(MFloat f2))))),
                                           CLog(CFrac(uval_to_cstr (Rc(U(MFloat (1.-.f1)))),uval_to_cstr (Rc(U(MFloat (1.-.f2))))))))))::Pc(Eqb(CSymB(x1), CSymB(x2)))::pc
  (* | Rc(P(MSymF(th1), MFloat(f2))) ->(m,Skip,ex,pc)
   * | Rc(P(MFloat(f), MSymF(th2))) -> (m,Skip,ex,pc)
   * | Rc(P(MSymF(th1), MSymF(th2))) -> (m,Skip,ex,pc) *)
  | _ -> failwith "Theta should be a symbolic float value or a float value or a pair of such. --->6"
 

let bern_neq m1 x theta ex pc=
  let x1=gen_fresh_sym() in
  let x2=gen_fresh_sym () in
  let eps=gen_fresh_sym () in
  let v=lookup m1 "epsilon_c" in
  let m=remove m1 "epsilon_c" in
  match theta with
  | Rc(U(MFloat(f))) ->
    ("epsilon_c", Rc(U(MSymF(eps))))::((x, Rc(P(MSymB(x1), MSymB(x2))))::m), Skip,
    ex, Pc(Eqf(CSymF(eps), COp(uval_to_cstr v, Add, CMax(CLog(CFrac(CFloat(f), CFloat(1.-.f))), CLog(CFrac(CFloat(1.-.f), CFloat(f)))))))::
        Pc(Neg(Eqb(CSymB(x1), CSymB(x2))))::pc
        
  (* | Rc(U(MSymF(_))) ->
   *   ("epsilon_c", Rc(U(MSymF(eps))))::((x, Rc(P(MSymB(x1), MSymB(x2))))::m), Skip,
   *   ex, Pc(Eqf(CSymF(eps), COp(uval_to_cstr v, Add, CFloat(0.0))))::Pc(Eqb(CSymB(x1), CSymB(x2)))::pc                            
   * | Rc(P(MFloat(f1), MFloat(f2))) ->
   *     ("epsilon_c", Rc(U(MSymF(eps))))::((x, Rc(P(MSymB(x1), MSymB(x2))))::m), Skip,
   *     ex, Pc(Eqf(CSymF(eps), COp(uval_to_cstr v, Add,
   *                                CMax(CLog(CFrac(uval_to_cstr (Rc(U(MFloat f1))),uval_to_cstr (Rc(U(MFloat f2))))),
   *                                          CLog(CFrac(uval_to_cstr (Rc(U(MFloat (1.-.f1)))),uval_to_cstr (Rc(U(MFloat (1.-.f2))))))))))::Pc(Eqb(CSymB(x1), CSymB(x2)))::pc *)
  (* | Rc(P(MSymF(th1), MFloat(f2))) ->(m,Skip,ex,pc)
   * | Rc(P(MFloat(f), MSymF(th2))) -> (m,Skip,ex,pc)
   * | Rc(P(MSymF(th1), MSymF(th2))) -> (m,Skip,ex,pc) *)
  | _ -> failwith "Theta should be a symbolic float value or a float value or a pair of such. --->7"
 
let bern_berndeltat m x e ex pc=(m, Skip, ex, pc)
let bern_deltatbern m x e ex pc=(m, Skip, ex, pc)
let bern_berndeltaf m x e ex pc=(m, Skip, ex, pc)
let bern_deltafbern m x e ex pc=(m, Skip, ex, pc)



let apply_all_bcouplings (m, x, e, ex, pc) = [
   (bern_eq m x e ex pc); 
  (bern_neq m x e ex pc);
  (* (bern_berndeltat m x e ex pc);(bern_berndeltaf m x e ex pc);
   * (bern_berndeltaf m x e ex pc);(bern_deltafbern m x e ex pc) *)
]

