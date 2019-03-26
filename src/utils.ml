open Ast
    
let global_counter = ref 0

let gen_fresh_sym = 
        fun () -> incr global_counter ; 
    Format.sprintf "X%i" !global_counter

let rec cstrfetosmt:  float cstre -> string= function 
  | CFloat(f) -> string_of_float f
  | CSymF(x) -> x
  | COp(e1, op, e2) -> Printf.sprintf "(%s %s %s)" (if op=Add then "+" else "-") (cstrfetosmt e1) (cstrfetosmt e2)
  | CLog(e1) -> Printf.sprintf "(log %s)" (cstrfetosmt e1)
  | CMax(e1, e2) -> Printf.sprintf "(max %s %s)" (cstrfetosmt e1) (cstrfetosmt e2)
  | CFrac(e1, e2) -> Printf.sprintf "(/ %s %s)" (cstrfetosmt e1) (cstrfetosmt e2)

let rec cstrbetosmt:  bool cstre -> string= function 
  | True -> "true"
  | CBool(b) -> string_of_bool b
  | CSymB(x) -> x

let rec cstrtosmt: bool cstr -> string= function
  | Assert(ce) ->
    begin
      match ce with
       | True -> " true \n"
       | CBool(b) -> ("( = "^(string_of_bool b)^" true )\n")
       | CSymB(x) -> ("( = "^x^" true)\n")
    end
  | Leq(e1, e2)-> Printf.sprintf "(<= %s %s)\n" (cstrfetosmt e1) (cstrfetosmt e2)
  | Neg(c) -> Printf.sprintf "(not %s)\n" (cstrtosmt c)
  | Eqf(e1, e2) -> Printf.sprintf "(= %s %s)\n"  (cstrfetosmt e1) (cstrfetosmt e2)
  | Eqb(e1, e2) -> Printf.sprintf "(= %s %s)\n" (cstrbetosmt e1) (cstrbetosmt e2) 


let extract (pc: bool condition)  = let Pc(v)=pc in v
let extractl (pc: bool path_condition)=List.map extract pc
    
let rec pctosmt: bool path_condition  -> string= fun pc ->
  (List.fold_left (fun t -> fun cstr -> t^(cstrtosmt cstr)) "(and \n" (extractl pc))^")"

type typed_sym=F of string | B of string

let rec get_typed_syms_from_expr: type a. a cstre -> typed_sym list =function
  | CSymB(x) ->  [B x]
  | CSymF(x) ->  [F x]
  | COp(e1,_,e2)->(get_typed_syms_from_expr e1)@(get_typed_syms_from_expr e2)
  | CLog(e1)-> (get_typed_syms_from_expr e1)
  | CMax(e1, e2)-> (get_typed_syms_from_expr e1)@(get_typed_syms_from_expr e2)
  | CFrac(e1, e2)-> (get_typed_syms_from_expr e1)@(get_typed_syms_from_expr e2)
  | _ -> []

let rec get_typed_syms_from_assertion: bool cstr -> typed_sym list =function
    | Assert(e)->get_typed_syms_from_expr e
    | Eqf(e1, e2) ->(get_typed_syms_from_expr e1)@(get_typed_syms_from_expr e2)
    | Eqb(e1, e2) ->(get_typed_syms_from_expr e1)@(get_typed_syms_from_expr e2)
    | Leq(e1, e2) ->(get_typed_syms_from_expr e1)@(get_typed_syms_from_expr e2)
    | Neg(e1) ->(get_typed_syms_from_assertion e1)
let get_typed_syms_from_list_assertion=fun t-> List.fold_left (fun y-> fun x-> (get_typed_syms_from_assertion x)@y)  []  t
    
let rec typesyms = function
  | [] -> ""
  | F(x)::l' -> (Printf.sprintf " (%s Real) " x)^(typesyms l')
  | B(x)::l' -> (Printf.sprintf " (%s Bool) " x)^(typesyms l')

   
