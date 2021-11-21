module Part1

open Parser
open FStar.String
open FStar.Printf
open FStar.IO
open FStar.All

type ast =
  | Number : n:int -> ast
  | Add : left:ast -> right:ast -> ast
  | Mul : left:ast -> right:ast -> ast
  | Paren : inner:ast -> ast

let rec print_ast (indent:string) (x:ast) : ML unit =
  match x with 
  | Number n -> print_string (sprintf "%s%d\n" indent n)
  | Add left right -> 
      print_string (indent ^ "(+\n");
      print_ast (indent ^ "  ") left;
      print_ast (indent ^ "  ") right;
      print_string (indent ^ ")\n")
  | Mul left right -> 
      print_string (indent ^ "(*\n");
      print_ast (indent ^ "  ") left;
      print_ast (indent ^ "  ") right;
      print_string (indent ^ ")\n")
  | Paren inner -> 
     print_string (indent ^ "[\n");
      print_ast (indent ^ "  ") inner;
      print_string (indent ^ "]\n")
      
let parse_number : parser ast =
  space (parse_apply (fun z -> Number z) unsigned_integer )

let token_plus : parser string =
  space (parse_forget (literal_char '+'))

let token_star : parser string =
  space (parse_forget (literal_char '*'))

let rec parse_ast (input:string) : Tot (parse_result ast input) (decreases (strlen input)) =
  parse_alternatives_ctx input
    [
      // These are tried in-order; we can't recurse into ast directly
      // ( ast ) + ast
      (binop_char_ctxe input 
         (brackets_char input '(' parse_ast ')' )
         token_plus 
         (space_ctx input parse_ast)
         (fun left right -> Add (Paren left) right));
      // ( ast ) * ast
      (binop_char_ctxe input 
         (brackets_char input '(' parse_ast ')' )
         token_star
         (space_ctx input parse_ast)
         (fun left right -> Mul (Paren left) right));
      // n + ast
      (binop_char_ctx input 
         parse_number token_plus 
         (space_ctx input parse_ast)
         (fun left right -> Add left right));
      // n * ast
      (binop_char_ctx input 
         parse_number token_star
         (space_ctx input parse_ast)
         (fun left right -> Mul left right));
      // (ast)   -- should only match at end?
      (parse_apply_ctxe 
        input
        (fun z -> Paren z) 
        (brackets_char input '(' parse_ast ')' ));
      parse_number 
    ]
    input

let parse_or_report_fail (x:(parser ast)) : ML unit =
  let line = input_line() in 
  match x line with
  | Success tree _ _ -> print_string "parsed!\n"; print_ast "" tree
  | ParseError expected at -> print_string( "expecting " ^ expected ^ " at '" ^ at ^ "'\n")

let _ = parse_or_report_fail parse_ast

(*
  
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
