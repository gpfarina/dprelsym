open Ast
open Utils

type  'a ucodel_w=
    MBool: bool -> bool ucodel_w
  | MFloat: float ->  float ucodel_w
  | MSymF: string  -> float ucodel_w
  | MSymB: string  -> bool ucodel_w

type ucodel=Uc: 'a ucodel_w -> ucodel


type 'a rcodel_w=
     P: 'a ucodel_w * 'a ucodel_w -> 'a rcodel_w
  | U: 'a ucodel_w -> 'a rcodel_w

type rcodel=Rc: 'a rcodel_w -> rcodel
  
type mem=(string * ucodel) list
type rmem=(string * rcodel) list


let string_of_ucodel_w: type a. a ucodel_w -> string=function
    MBool(b)->string_of_bool b
  | MFloat(f)->string_of_float f
  | MSymF(x)->x
  | MSymB(x)->x


let proj_rcodel_l rel=
   match rel with
   | (x, Rc(U(el)))-> (x, Uc(el))
   | (x, Rc(P(el1, _))) ->(x, Uc(el1))
let proj_rcodel_r rel=
   match rel with
   | (x, Rc(U(el)))-> (x, Uc(el))
   | (x, Rc(P(_, el1))) ->(x, Uc(el1))

let proj_mem_r rm =
  List.map proj_rcodel_r rm
let proj_mem_l rm =
  List.map proj_rcodel_l rm

let lookup m x = snd (List.find (fun (n, _)-> n=x) m)

let remove m x=
  List.filter (fun (n, _)-> n<>x) m
    
let merge_el el1 el2 =
  if el1=el2 then let (Uc(d))=el1 in Rc(U(d))
  else match (el1, el2) with
    | Uc(MBool(b1)), Uc(MBool(b2)) ->Rc(P(MBool(b1), MBool(b2)))
    | Uc(MSymB(x)), Uc(MSymB(y)) -> Rc(P(MSymB(x), MSymB(y)))
    | Uc(MBool(b)), Uc(MSymB(x)) ->Rc(P(MBool(b), MSymB(x)))
    | Uc(MSymB(x)), Uc(MBool(b)) ->Rc(P(MSymB(x), MBool(b)))
    | Uc(MFloat(f1)), Uc(MFloat(f2)) ->Rc(P(MFloat(f1), MFloat(f2)))
    | Uc(MFloat(f)), Uc(MSymF(y)) -> Rc(P(MFloat(f), MSymF(y)))
    | Uc(MSymF(x)), Uc(MFloat(f)) -> Rc(P(MSymF(x), MFloat(f)))
    | Uc(MSymF(x)), Uc(MSymF(y)) ->Rc(P(MSymF(x), MSymF(y)))
    | _ -> failwith "It should not happen. --> 5"
  
let merge_mem m1 m2=
 let module SS = Set.Make(String) in
 let dom1=SS.of_list (List.map (fun (x, _) -> x) m1) in
 let dom2=SS.of_list (List.map (fun (x, _) -> x) m2) in
 let dom=SS.union dom1 dom2 in 
 let ldom=SS.elements dom in

 let f= (fun x -> 
     try
       begin
        let Uc(v1)= lookup m1 x in
        try begin
          let Uc(v2)=lookup m2 x in
          (x, merge_el (Uc(v1)) (Uc(v2)))
        end
        with Not_found -> (x, Rc(U(v1)))
      end
     with
      | Not_found ->
        begin
          try
            let Uc(v2)=lookup m2 x in   (x, Rc(U(v2)))
          with
           Not_found -> failwith "A variable is in the domain but does not have a value"
        end
     ) in
   List.map f ldom

      

    
let make_implication (m: rmem) (p: bool path_condition)=
  let module Typed = Set.Make(struct type t = typed_sym let compare = compare end)in
  let varset= Typed.elements (Typed.of_list (get_typed_syms_from_list_assertion (extractl p))) in
  let Rc(v1)=(lookup m "out") in
  let (so1, so2)=
    (match v1 with
     | U(t) -> string_of_ucodel_w t,string_of_ucodel_w t
     | P(t1, t2)  ->string_of_ucodel_w t1,string_of_ucodel_w t2 )
  in
  let eps,epsc=
    match lookup m "eps", lookup m "epsilon_c" with
    |Rc(U(t1)), Rc(U(t2))-> string_of_ucodel_w t1, string_of_ucodel_w t2
    | _-> failwith "Should not happen"
  in
  let Rc(input)=lookup m "input" in
  let additional=(match input with
  | U(MSymF(x))->[F x]
  | U(MSymB(x))->[B x]
  | P(MSymF(x), MSymF(y))->[F x; F y]
  | P(MSymB(x), MSymB(y))->[B x; B y]
  | _-> failwith "Input mistyped in the two runs"
  )
in
  Printf.sprintf
    "(assert (not (forall (%s) (=> %s (and (= %s %s) (<= %s %s))))))"
    (typesyms (Typed.elements (Typed.of_list(additional@varset))))
    (pctosmt p)
    so1 so2
    epsc eps
