open Utils
open Ast
open Mem
open Ustep
open Rexp
open Bcouplings
type var=string

let rec rstep: rmem-> cmd-> var list -> bool path_condition -> (rmem * cmd * var list * bool path_condition) list =
  fun m-> fun c -> fun ex->fun pc ->
    match c with
  | Ass(x, e) -> let (v, pc')=reval m e pc in let m'=remove m x in [((x, v)::m', Skip, ex, pc')]
  | Ite(g, ct, cf) ->
    begin
      let (Rc(v), pc') = reval m g pc in
      match  v with
      |U(MBool(true)) -> [(m,ct, ex, pc')]
      |P(MBool(true), MBool(true)) -> [(m,ct, ex, pc')] (*it should not happen ...*)
      |U(MBool(false)) ->[(m,cf, ex, pc')]
      |P(MBool(false), MBool(false)) -> [(m,cf, ex, pc')] (*it should not happen ...*)
      |U(MSymB(x)) ->[(m,ct, ex, Pc(Assert(CSymB(x)))::pc');(m,cf, ex, Pc(Neg(Assert(CSymB(x))))::pc')] 
      |P(MSymB(x),MBool(true))-> [(m,ct, ex, Pc(Assert(CSymB(x)))::pc');(m, Pair(cproj_l cf, cproj_r ct), ex, Pc(Neg(Assert(CSymB(x))))::pc')]
      |P(MBool(true), MSymB(x))->  [(m,ct, ex, Pc(Assert(CSymB(x)))::pc');(m, Pair(cproj_l ct, cproj_r cf), ex, Pc(Neg(Assert(CSymB(x))))::pc')]
      |P(MSymB(x),MBool(false))-> [(m,cf, ex, Pc(Neg(Assert(CSymB(x))))::pc');(m, Pair(cproj_l ct, cproj_r cf), ex, Pc(Assert(CSymB(x)))::pc')]
      |P(MBool(false), MSymB(x))->  [(m,cf, ex, Pc(Neg(Assert(CSymB(x))))::pc');(m, Pair(cproj_l cf, cproj_r ct), ex, Pc(Assert(CSymB(x)))::pc')]
      |P(MSymB(x), MSymB(y))-> [
          (m,ct, ex, Pc(Assert(CSymB(x)))::Pc(Assert(CSymB(y)))::pc');
          (m,cf, ex, Pc(Neg(Assert(CSymB(x))))::Pc(Neg(Assert(CSymB(y))))::pc');
          (m, Pair(cproj_l ct, cproj_r cf), ex,  Pc(Assert(CSymB(x)))::Pc(Neg(Assert(CSymB(y))))::pc');
          (m, Pair(cproj_l cf, cproj_r ct), ex,  Pc(Neg(Assert(CSymB(x))))::Pc(Assert(CSymB(y)))::pc')
        ]
      | _ -> failwith "Guard should be a boolean. -->4"
    end    
  | Seq(Skip, c2) -> [(m, c2, ex, pc)]
  | Seq(c1, c2) ->
    begin
      let lc=rstep m c1 ex pc in
      List.map (fun (m1', c1', ex, pc')-> (m1', Seq(c1', c2), ex , pc')) lc
    end
  | Pair(USkip, USkip) -> [(m,Skip, ex, pc)]
  | Pair(USkip, cr) ->
    begin
      let ml,mr=proj_mem_l m, proj_mem_r m in
      let (m2', c2', pc')=ustep mr cr pc in
      [(merge_mem ml m2', Pair(USkip, c2'), ex, pc')]
    end
  | Pair(cl, cr) ->
    begin
      let ml,mr=proj_mem_l m, proj_mem_r m in
      let (ml', c1', pc')=ustep ml cl pc in
      [(merge_mem ml' mr, Pair(c1', cr), ex, pc')]
    end
  | Skip -> failwith "This function should not be called with Skip. -->5"
  | RndAss(_) -> failwith "This function should not be called with RndAss. -->6"
  

let rec rtrans:  (rmem * cmd * var list * bool path_condition) list -> (rmem * cmd * var list *bool path_condition) list = fun l ->
  match l with
  | [] -> []
  | (_, RndAss(_), _, _)::l' -> l
  | (_, Seq(RndAss(_), _), _, _)::l' -> l
  | (m, Skip, ex, pc) :: l'-> (m, Skip, ex, pc)::rtrans l'
  | (m, c, ex, pc)::l'->rtrans(rstep m c ex pc@ l')

let rec chk_final=List.for_all (fun (_,c,_,_) -> if c=Skip then true else false) 

            
let rec rtranstrans:  (rmem * cmd * var list * bool path_condition) list list -> (rmem * cmd * var list * bool path_condition) list list= fun l ->
  match l with
  | [] -> []
  | l::tll ->
    begin
      if chk_final l then l::rtranstrans tll
      else
        begin
          match l with
          | [] -> rtranstrans tll
          | (m,RndAss(x, e), ex, pc)::tl->
            let v,pc'=reval m e pc in 
            let lcoupled=(apply_all_bcouplings (m, x, v, ex, pc')) in
            let newproofs=List.map (fun ppf -> ppf::tl ) lcoupled in
            rtranstrans (newproofs@tll)
          | (m,Seq(RndAss(x, e), c2), ex, pc)::tl->
            let v,pc'=reval m e pc in 
            let lcoupled=(apply_all_bcouplings (m, x, v, ex, pc')) in
            let newproofs=List.map (fun ppf -> ppf::tl ) (List.map (fun (mt, cmdt, vart, pct) -> (mt, Seq(cmdt, c2), vart, pct)) lcoupled) in
            rtranstrans (newproofs@tll)
          | (m, c, ex, pc):: tl ->rtranstrans ((rtrans l)::tll)
        end
    end
