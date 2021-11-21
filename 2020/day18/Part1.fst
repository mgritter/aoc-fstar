module Part1

open Parser
open FStar.String
open FStar.IO
open FStar.All

(*
type ast =
  | Number : n:int -> ast
  | Add : left:ast -> right:ast -> ast
  | Mul : left:ast -> right:ast -> ast

*)
(*
let parse_number : parser ast =
  space (parse_apply (fun z -> Number z) unsigned_integer )
 *)

let rec parse_recursive (input:string) : Tot (parse_result string input) (decreases strlen(input)) =
    (parse_either_ctx input
      (parse_forget (literal_char 'x'))
      (brackets_char input '(' parse_recursive ')'))
      input

let parse_or_report_fail (x:(parser string)) : ML unit =
  let line = input_line() in 
  match x line with
  | Success tok _ _ -> print_string ("parsed '" ^ tok ^ "'\n" )
  | ParseError expected at -> print_string( "expecting " ^ expected ^ " at '" ^ at ^ "'\n")

let _ = parse_recursive <: parser string
  
let _ = parse_or_report_fail parse_recursive  

(*
let rec parse_ast (input:string) : Tot (parse_result ast input) (decreases (strlen input)) =
  parse_either
    (parse_literal )
    (brackets "(" parse_ast ")" )
    input
  *)
  
  (*
  <|>
  ( parse_comb 
     parse_ast 
     (fun t1 t2 -> (Add t1 t2))
     (parse_comb
       (literal "+")
       (fun op t2 -> t2)       
       parse_ast ))
       
*)
