open Uexp
open Utils
open Ast
open Mem
    
let rec ustep:  mem-> ucmd-> bool path_condition -> (mem * ucmd * bool path_condition) = fun m-> fun c -> fun pc -> 
  match c with
  | USkip -> (m, USkip, pc)
  | UAss(x, e) -> let (v, pc')=ueval m e pc in let m'=remove m x in ((x, v)::m', USkip, pc')
  | USeq(USkip, c2) -> (m, c2,pc) 
  | USeq(c1, c2) -> let (m',c1',pc')=ustep m c1 pc in (m', USeq(c1', c2), pc')



