open Ast
open Utils
open Mem
open Uexp
open Rexp
open Ustep
open Rstep


let theory="(declare-fun log (Real) Real)
(define-fun max ((x1 Real) (x2 Real)) Real
   (ite (<= x1 x2) x2 x1))
(assert (forall ((a Real) (b Real))
        (and
                (=> (<= a b) (<= (log a) (log b)))
                (=> (and (>= a 0) (>= b 0) )
                        (>= (+ (log a) (log b)) (log a))
                (= (log 1.0) 0.0)
                (=> (< a 1) (< (log a) 0))
                (=> (> a 1) (> (log a) 0))
                )
        )
)
)
\n"


let exec c=
  let res: ((string*rcodel) list*cmd*var list * bool path_condition)list list=
    rtranstrans [[([("eps", Rc(U(MSymF("EPS"))));("epsilon_c", Rc(U(MFloat(0.0))))], c, [],
                   [Pc(Neg(Eqb(CSymB("I1"), CSymB("I2"))));Pc(Eqf(CSymF("EPS"), CLog(CFloat(2.))))])]] in
  let proofs=List.map  (fun l1-> List.map (fun (m,_,_,s) -> make_implication m s) l1) res
  in
  let _ =
    List.mapi  ( fun i-> fun lel ->
        List.mapi ( fun j->fun el ->
            let oc = open_out (Printf.sprintf "test/proof%d-assertion%d.z3" i j) in
            output_string oc theory;
            output_string oc (el^"\n");
            output_string oc "(check-sat)";
          close_out oc ) lel ) proofs in ()

let rr=Seq(Ass("input", RPair(Value(SymB("I1")),Value(SymB("I2")))),
            Seq(RndAss("f", RValue(Float(0.75))), Ite(RVar("f"),Ass("out", RVar("input")), Ass("out", RNeg(RVar("input"))))))

let _=exec rr
