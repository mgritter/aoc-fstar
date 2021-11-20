module Parser

open FStar.String
open FStar.Printf
open Suffixes

// The type returned by a parser.
// The parser may consume some of the input string, and returns the rest,
// which must be a suffix of the input.
type parse_result 'a (input:string) =
  | ParseError : expecting:string -> at:string -> parse_result 'a input
  | Success : v:'a -> consumed:nat -> rest:string{is_suffix_at rest input consumed} -> parse_result 'a input

let parser (a:Type) = (x:string) -> Tot (parse_result a x)

let err_or_shorter #a (input:string) (r:parse_result a input) : bool =
  match r with
  | Success _ consumed _ -> consumed > 0
  | ParseError _ _ -> true
  
let shorter_result (a:Type) (input:string) = (r:(parse_result a input){err_or_shorter input r})

let proper_parser (a:Type) = (x:string) -> Tot (r:(parse_result a x){err_or_shorter x r})

(*
  The most general combinator: apply a function to the results of two parsers.
  Takes a function to combine two parse results from two types into a third type.  
*)
let parse_comb #a #b #c (x:(parser a)) (f: a -> b -> Tot c) (y:(parser b)) (input:string) : Tot (parse_result c input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 c1 rest -> match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2
      | Success t2 c2 r2 -> 
        (suffix_transitivity r2 c2 rest c1 input;
        Success (f t1 t2) (c1+c2) r2)

let parse_comb1 #a #b #c (x:(proper_parser a)) (f: a -> b -> Tot c) (y:(parser b)) (input:string) : Tot (shorter_result c input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 c1 rest -> match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2
      | Success t2 c2 r2 -> 
        (suffix_transitivity r2 c2 rest c1 input;
        Success (f t1 t2) (c1+c2) r2)

(*
 handling literals
 *)
 
let literal (tok:string{strlen tok>0}) (input:string) : Tot (r:(parse_result (z:string{z=tok}) input){err_or_shorter input r}) (decreases (strlen input))= 
  if strlen tok > strlen input then
     ParseError (sprintf "literal '%s'" tok) input
  else let m = sub input 0 (strlen tok) in
     if m = tok then
        Success m (strlen tok) (suffix_at input (strlen tok))
     else
        ParseError (sprintf "literal '%s'" tok) input

let bar_tok : (s:string{strlen s=3}) = assert_norm( strlen "bar" = 3); "bar"
let foo_tok : (s:string{strlen s>0}) = assert_norm( strlen "foo" > 0); "foo"

(* The more-specific type means it's not a parser string, it's
   a more specific parser.*)
let _ = literal foo_tok <: (parser (z:string{z="foo"}))
[@@expect_failure]
let _ = literal foo_tok <: (parser string)

// Return the value inside of the given brackets
let brackets #a (lbracket:string{strlen lbracket > 0}) (x:parser a) (rbracket:string{strlen rbracket >0}) (input:string) : Tot (shorter_result a input) (decreases (strlen input)) =
  parse_comb1 
    (literal lbracket)
    (fun t1 t2 -> t2 )
    (parse_comb
      x
      (fun t2 t3 -> t2 )
      (literal rbracket))
  input

(*
 Manipulating the result of a parser: applying a function on success,
 switching to a less-specific type, or renaming the failure condition.
 *)
 
// Transform the result of a single parser
let parse_apply #a #b (f:a->b) (x:(parser a)) (input:string): Tot (parse_result b input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 c1 rest -> Success (f t1) c1 rest

// Forget refined types in the parse result
let parse_forget #a #p (x:(parser (z:a{p z}))) (input:string) : Tot (parse_result a input) =
    parse_apply id x input

// Rename the failure condition on parsing
let parse_rename #a (e:string) (x:(parser a)) (input:string) : Tot (parse_result a input) =
  match (x input) with
  | Success v c1 rest -> Success v c1 rest
  | ParseError _ at -> ParseError e at

(* 
 Combinators for two parsers
*)

// Combine two possible errors into a parse error
let or_of_reasons #a #i (r1:string) (r2:string) (at:string) 
  :  (r:(parse_result a i){ParseError? r}) =
  ParseError (concat " or " [r1; r2]) at
    
// Parse one of two options of the same type. Does not indicate which was chosen,
// you'll have to have the value indicate that.
let parse_either #a (x:(parser a)) (y:(parser a)) (input:string) : Tot (parse_result a input) =
  match (x input) with
  | Success t1 c1 rest -> Success t1 c1 rest
  | ParseError e1 a1 -> match (y input) with
     | Success t2 c2 r2 -> Success t2 c2 r2 
     | ParseError e2 a2 -> or_of_reasons e1 e2 input

// Parse an entire list of the same type
let rec parse_alternatives #a (x:list(parser a){Cons? x}) (input:string) : Tot (parse_result a input) =
  match x with
  | hd :: [] -> (hd input)
  | hd :: tl -> (parse_either hd (parse_alternatives tl) input) 

// Parse two alternatives with differing refined types
let parse_either_relax #a #pa #pb 
   (x:(parser (z:a{pa z}))) 
   (y:(parser (z:a{pb z}))) 
   (input:string) : Tot (parse_result (z:a{pa z \/ pb z}) input) =
  match (x input) with
  | Success t1 c1 rest -> Success t1 c1 rest
  | ParseError e1 a1 -> match (y input) with
     | Success t2 c2 r2 -> Success t2 c2 r2 
     | ParseError e2 a2 -> or_of_reasons e1 e2 input

// <|> to create alternatives using the relaxed semantics
let op_Less_Bar_Greater #a #pa #pb
   (x:(parser (z:a{pa z}))) 
   (y:(parser (z:a{pb z}))) = 
  parse_either_relax x y

// Parse a list of one type, then a second list of the same type, and append them
let parse_list #a (x:(parser (list a))) (y:(parser (list a))) (input:string) : Tot (parse_result (list a) input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 c1 rest -> match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2 
      | Success t2 c2 r2 -> 
        (suffix_transitivity r2 c2 rest c1 input;
         Success (FStar.List.Tot.append t1 t2) (c1+c2) r2)

// Parsing a nonempty list, followed by a possibly empty list, gives a nonempty list.
// TODO: how to combine that with the above definition?
let parse_nonempty_list #a (x:(parser (z:(list a){Cons? z}))) (y:(parser (list a))) (input:string) : Tot (parse_result (z:(list a){Cons? z}) input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 c1 rest -> match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2 
      | Success t2 c2 r2 -> 
        (suffix_transitivity r2 c2 rest c1 input;
         Success (FStar.List.Tot.append t1 t2) (c1+c2) r2)

(* 
 Optional and repeated types 

// The Kleene star won't terminate if the parser doesn't consume input.  So, we'll
// enforce totality by exiting as soon as it doesn't. 
// (Previous approach: define proper and improper parsers, but then we'd have to have
// make multiple version of the above combinators, probably?)
let rec parse_star_aux #a (input:string) (x:parser a) (prev_a:list a) 
: Tot ((list a)*(remaining:string{is_suffix remaining input})) 
  (decreases (strlen input)) =
  match (x input) with
  | ParseError _ at -> 
     suffix_is_reflexive input;
     ((List.Tot.rev prev_a),input)
  | Success v rest -> 
     if rest = input then ((List.Tot.rev prev_a),input)
       else ( suffix_is_shorter rest input;
              suffix_is_substring rest input;
              proper_substring rest input;
              let next_match = parse_star_aux rest x (v :: prev_a) in
                ( suffix_transitivity (snd next_match) rest input;
                  assert( is_suffix (snd next_match) input );
                  // OK, this is dumb, F* knows about (snd next_match) but it
                  // can't apply that to intrinsic type of the pair without
                  // me spelling it out for it.
                  ((fst next_match), (snd next_match)) ) )

// Parse zero or more of the given parser, returned as a list
let parse_star #a (x:(parser a)) (input:string): Tot (parse_result (list a) input) =
    let r = parse_star_aux input x [] in
       Success (fst r) (snd r)

let listify #a (x:a) : y:(list a){Cons? y} = [x]

// Parse one or more of the given parser, returned as a list
let parse_plus #a (x:(parser a)) : Tot (parser (z:(list a){Cons? z})) =
  parse_nonempty_list (parse_apply listify x) (parse_star x)

// Parse zero or one of the given parser, returned as an option
let parse_option #a (x:(parser a)) (input:string): Tot (parse_result (option a) input) =
  match (x input) with
  | Success v rest -> Success (Some v) rest
  | ParseError _ _ -> 
    suffix_is_reflexive input;
    Success None input


type digit_string = (x:string{x = "0" \/ x = "1" \/ x = "2" \/ x = "3" \/ x = "4" \/ x = "5" \/ x = "6" \/ x = "7" \/ x = "8" \/ x = "9"})

// This definition fails if one of the possibilities is missing!
// ... or out of order.  Exciting!
let digit : (parser digit_string) =
    parse_rename "digit" (literal "0" <|> literal "1" <|> literal "2" <|> literal "3" <|> literal "4" <|> literal "5" <|> literal "6" <|> literal "7" <|> literal "8" <|> literal "9")

let digit_string_to_int (d:digit_string) : int = 
  match d with
  | "0" -> 0
  | "1" -> 1
  | "2" -> 2
  | "3" -> 3
  | "4" -> 4
  | "5" -> 5
  | "6" -> 6
  | "7" -> 7
  | "8" -> 8
  | "9" -> 9

let rec dl_to_int_aux (remaining_digits : list digit_string) (prev:int) : int =
  match remaining_digits with
  | [] -> prev
  | hd :: tl -> dl_to_int_aux tl ((op_Multiply 10 prev) + (digit_string_to_int hd))
     
let dl_to_int (d : list digit_string{Cons?d}) : int =
  dl_to_int_aux d 0

// TODO: prove that dl_to_int is the inverse of printing an unsigned integer

// Parse an unsigned decimal 
let unsigned_integer : parser int = 
    parse_rename "unsigned integer" 
      (parse_apply dl_to_int (parse_plus digit))

// Parse a signed decimal (only - is recognized, not +)
let signed_integer : parser int = 
    parse_rename "integer"
      (parse_comb 
        (parse_option (literal "-"))
        (fun o i -> match o with
         | Some _ -> op_Multiply (-1) i
         | None -> i)
        unsigned_integer)
        
// Consume any space and go on to the next parser
// TODO: work on any whitespace characters
let space #a (x:parser a) : parser a =
    parse_comb
      (parse_star (literal " "))
      (fun ws result -> result)
      x


*)





