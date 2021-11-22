module Part2

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

let at_end #a (x:(parser a)) (input:string) : Tot (parse_result a input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success v1 c1 r1 -> 
     if strlen r1 = 0 then Success v1 c1 r1
     else ParseError "end of file" r1

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

//  A + B * C + D 
//  parses as
//  (add A (mul B (add C D))) 
//  but in evaluation order it should be
//  (mult (add A B) (add C D))

let rec rewrite_prec (tree:ast) : Tot ast =
    match tree with
    | Number n -> Number n 
    | Paren p -> (rewrite_prec p)
    // Addition is higher precendence, so if we have
    // A+B*C, then we need to add A to the first argument of the
    // next term first
    | Add a t -> rewrite_add (rewrite_prec a) t
    | Mul a t -> rewrite_mul (rewrite_prec a) t
and rewrite_add (left_op:ast) (tree:ast) : Tot ast (decreases tree) =
    match tree with
    | Number n -> (Add left_op (Number n))
    | Paren p -> (Add left_op (rewrite_prec p))
    | Add a t -> rewrite_add (Add left_op (rewrite_prec a)) t
    | Mul a t -> rewrite_mul (Add left_op (rewrite_prec a)) t
and rewrite_mul (left_op:ast) (tree:ast) : Tot ast (decreases tree) = 
    match tree with
    | Number n -> (Mul left_op (Number n))
    | Paren p -> (Mul left_op (rewrite_prec p))    
    // Here's where the change comes in, we need to do the addition first, and
    // defer the multiplication until later
    | Add a t -> (Mul left_op (rewrite_add (rewrite_prec a) t))
    | Mul a t -> rewrite_mul (Mul left_op (rewrite_prec a)) t

let rec eval (tree:ast) : int =
    match tree with
    | Number n -> n
    | Paren p -> (eval p)
    | Add a t -> (eval a) + (eval t)
    | Mul a t -> op_Multiply (eval a) (eval t)

let parse_and_rewrite (x:(parser ast)) : ML unit =
  let line = input_line() in 
  match x line with
  | Success tree _ _ -> 
       print_string "parsed!\n"; 
       print_ast "" tree;
       let rw = rewrite_prec tree in
          print_string "rewritten:\n";
          print_ast "" rw;
          print_string "evaluated:\n";
          print_string (sprintf "%d\n" (eval rw))
  | ParseError expected at -> print_string( "expecting " ^ expected ^ " at '" ^ at ^ "'\n")

// let _ = parse_and_rewrite parse_ast

let rec parse_and_sum_aux (fd:fd_read) (sum:int) : ML int =
  try 
    let line = read_line fd in
       match (parse_ast line) with
         | ParseError p e ->
           print_string "parse error\n"; 0
         | Success tree _ _ ->           
            let n = eval (rewrite_prec tree) in
             print_string (sprintf "%s == %d\n" line n );
             parse_and_sum_aux fd (sum + n)
  with
    | EOF -> sum
    | _ -> print_string "unexpected error\n"; 0
    
let parse_and_sum (fn:string) : ML unit =
  let fd = open_read_file fn in
    let sum = parse_and_sum_aux fd 0 in
      print_string (sprintf "Total: %d\n" sum)

//let _ = parse_and_sum "example.txt"
let _ = parse_and_sum "input.txt"


