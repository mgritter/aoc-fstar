module Part1

open FStar.IO
open FStar.All
open FStar.String
open FStar.Printf

// [] {} <> ()
type parse_stack =
 | Empty : parse_stack
 | Square : prev:parse_stack -> parse_stack
 | Curly : prev:parse_stack -> parse_stack
 | Angle : prev:parse_stack -> parse_stack
 | Paren : prev:parse_stack -> parse_stack

// Returns the first character that doesn't match the matching open
let rec parse_line (input:list char) (stack:parse_stack) : (option char) =
  match input with 
  | [] -> None
  | c :: rest ->
    match c with
    | '[' -> parse_line rest (Square stack)     
    | ']' -> if Square? stack then parse_line rest (Square?.prev stack) 
       else Some ']'
    | '(' -> parse_line rest (Paren stack)     
    | ')' -> if Paren? stack then parse_line rest (Paren?.prev stack) 
       else Some ')'
    | '<' -> parse_line rest (Angle stack)     
    | '>' -> if Angle? stack then parse_line rest (Angle?.prev stack) 
       else Some '>'
    | '{' -> parse_line rest (Curly stack)     
    | '}' -> if Curly? stack then parse_line rest (Curly?.prev stack) 
       else Some '}'
    | c -> Some c

let score (illegal:option char) : int =
   match illegal with
 | None -> 0
 | Some ']' -> 57
 | Some '}' -> 1197
 | Some '>' -> 25137
 | Some ')' -> 3
 | Some _ -> 0

(*
): 3 points.
]: 57 points.
}: 1197 points.
>: 25137 points.
*)

let parse_and_print (s:string) : ML (option char) =
   let r = parse_line (list_of_string s) Empty in
    (  match r with
   | None -> print_string (sprintf "%s none\n" s)
   | Some c -> print_string (sprintf "%s %c\n" s c)
   ) ; r
      
let rec parse_input (fd:fd_read) : ML int =
   try
     let l = (read_line fd) in 
       let s = parse_and_print l in
         score s + (parse_input fd)
   with
   | EOF -> 0
   | _ -> failwith "unknown error"

let calc_part_1 (fn:string) : ML unit =
  let fd = open_read_file fn in
    let s = parse_input fd in
        print_string (sprintf "%d\n" s )

let _ = calc_part_1 "example.txt"
let _ = calc_part_1 "input.txt"
