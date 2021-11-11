module Parser

(*
A very simple parser combinator library.

Parsers are functions that take a string and return a parse_result which
contains either a user-specified value and the remaining portion of the string,
or the parse_error type.
*)

open FStar.String
open FStar.Printf

// The type returned by a parser
type parse_result 'a =
  | ParseError : expecting:string -> at:string -> parse_result 'a
  | Success : v:'a -> rest:string -> parse_result 'a

// Need to define substrings to state that the parser consumes
// a portion of the input and leaves the rest.
let is_proper_substring (a:string) (b:string) : bool = 
  if strlen a = 0 then false else
  if strlen a > strlen b then false else
  (sub b 0 (strlen a)) = a

let proper_substring_is_shorter (a:string) (b:string) 
  : Lemma (requires (is_proper_substring a b))
          (ensures (strlen a) < (strlen b) )
           = admit()
        
// Lemma: a substring of a substring is a substring
let substring_transitivity (a:string) (b:string) (c:string) :
  Lemma (requires (is_proper_substring a b) && (is_proper_substring b c))
        (ensures (is_proper_substring a c)) 
          = admit()

// The type of a parser 
type parser 'a = (x:string) -> Tot (parse_result 'a)

// A parser that is guaranteed to consume at least one unit
type proper_parser 'a = (x:string) -> Tot (r:(parse_result 'a){ParseError? r ||
  is_proper_substring (Success?.rest r) x})

// Parse one type, then a second, and return a pair
let parse_seq #a #b (x:(proper_parser a)) (y:(proper_parser b)) : Tot (proper_parser (a*b)) =
  fun (input:string) -> 
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 rest ->
    match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2
      | Success t2 r2 -> 
        ( substring_transitivity r2 rest input;
          Success (t1, t2) r2 )

//  <,> to create pairs
let op_Less_Comma_Greater (#a:Type) (#b:Type) (x:proper_parser a) (y:proper_parser b) = 
  parse_seq #a #b x y

// Parse a list of one type, then a second list of the same type, and append them
let parse_list #a (x:(proper_parser (list a))) (y:(proper_parser (list a))) : Tot (proper_parser (list a)) =
  fun (input:string) -> 
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 rest -> match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2 
      | Success t2 r2 -> 
        (substring_transitivity r2 rest input;
         Success (FStar.List.Tot.append t1 t2) r2)

// <::> to create lists
let op_Less_Colon_Colon_Greater (#a:Type) (x:proper_parser (list a)) (y:proper_parser (list a)) =
  parse_list #a x y

// Explicitly combine the parse results from two types into a third
let parse_comb #a #b #c (x:(proper_parser a)) (f: a -> b -> Tot c) (y:(proper_parser b)) : Tot (proper_parser (c)) =
  fun (input:string) -> 
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 rest -> match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2
      | Success t2 r2 -> 
        (substring_transitivity r2 rest input;
        Success (f t1 t2) r2)

// Don't think we can create a ternary operator, but somebody could define their own
// based on a specific method of combining the parsed types

// A utility function for replacing parser failure positions
val bound_string_length : (s:string) -> (l:nat{l>=3}) -> Tot (t:string{strlen t <= l})
let bound_string_length s l = 
  if (strlen s) <= l then  s
  else 
    ( concat_length (sub s 0 (l-3)) "...";  // lemma from String module
      assert_norm( (strlen "...") == 3 );   // let F* know how long the string is?
     (sub s 0 (l-3)) ^ "..." )

let or_of_reasons #a (r1:string) (r2:string) (at:string) 
  :  (r:(parse_result a){ParseError? r}) =
  ParseError (concat " or " [r1; r2]) at
    
// Parse one of two options of the same type. Does not indicate which was chosen,
// you'll have to have the value indicate that.
let parse_either #a #b (x:(parser a)) (y:(parser a)) : Tot (parser a) =
  fun (input:string) -> 
  match (x input) with
  | Success t1 rest -> Success t1 rest
  | ParseError e1 a1 -> match (y input) with
     | Success t2 r2 -> Success t2 r2 
     | ParseError e2 a2 -> or_of_reasons e1 e2 input

type left_right 'a 'b =
 | Left : left:'a -> left_right 'a 'b
 | Right :  right:'b -> left_right 'a 'b
 
// Parse one of the options of differing types.  Indicate which was chosen with the
// left_right type.
let parse_lr #a #b (x:(proper_parser a)) (y:(proper_parser b)) : Tot (proper_parser (left_right a b)) =
  fun (input:string) -> 
  match (x input) with
  | Success t1 rest -> Success (Left t1) rest
  | ParseError e1 a1 -> match (y input) with
     | Success t2 r2 -> Success (Right t2) r2 
     | ParseError e2 a2 -> or_of_reasons e1 e2 input

// We can only parse a Kleene star if the parser guarantees it consumes at least one
// token of the input each time.
let rec parse_star_aux #a (input:string) (x:proper_parser a) (prev_a:list a) 
: Tot (list a*string) (decreases (strlen input)) =
  match (x input) with
  | ParseError _ at -> ((List.Tot.rev prev_a),at)
  | Success v rest -> 
     proper_substring_is_shorter rest input;
     parse_star_aux rest x (v :: prev_a)

// Parse zero or more of the given parser, returned as a list
let parse_star #a (x:(proper_parser a)) : Tot (parser (list a)) =
  fun (input:string) -> 
     let r = parse_star_aux input x [] in
       Success (fst r) (snd r)

(*
  Parsers for basic types
*)

// Return the string when the string is matched.
let literal (a:string) (input:string) : Tot (parse_result string) =
  if strlen a > strlen input then
     ParseError (sprintf "literal '%s'" a) input
  else let m = sub input 0 (strlen a) in
     if m = a then
        Success m (sub input (strlen a) ((strlen input) - (strlen a)))
     else
        ParseError (sprintf "literal '%s'" a) input

// Return a specific value when the string is matched
let literal_of #b (a:string) (v:b) (input:string) : Tot (parse_result b) =
  match literal a input with
  | ParseError expected at -> ParseError expected at
  | Success _ rest -> Success v rest

(*
let integer (input:string) : Tot (parse_result int) = 
  *)


  




