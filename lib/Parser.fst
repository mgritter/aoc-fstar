module Parser

open FStar.String
open FStar.Printf
open Suffixes

// The type returned by a parser.
// The parser must consume some of the input string, and returns the rest,
// which must be a suffix of the input.
type parse_result 'a (input:string) =
  | ParseError : expecting:string -> at:string -> parse_result 'a input
  | Success : v:'a -> consumed:nat{consumed > 0} -> rest:string{is_suffix_at rest input consumed} -> parse_result 'a input

// Unconstrainted parser which can take any string (useful at the top level for non-recursive types)
let parser (a:Type) = (x:string) -> Tot (parse_result a x)

// Parsers which constraint the input side to be < or <= a context which was a previous input
// from a higher level of the recursions.
let parser_ctx (a:Type) (prev_input:string) = (x:string{strlen x < strlen prev_input}) -> Tot (parse_result a x)
let parser_ctxe (a:Type) (prev_input:string) = (x:string{strlen x <= strlen prev_input}) -> Tot (parse_result a x)

(*
  The most general combinator: apply a function to the results of two parsers.
  Takes a function to combine two parse results from two types into a third type.

  A previous input (of which the input is a prefix, although we only measure its length)
  must be provided in order to take parser_ctx as either the first, second, or both arguments.
*)

// First argument is an unconstrained parser
// So we can take <= because it can't recurse
let parse_comb1 #a #b #c (prev_input:string)
  (x:parser a) (f: a -> b -> Tot c) (y:parser_ctx b prev_input) 
  (input:string{strlen input <= strlen prev_input}) : Tot (parse_result c input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 c1 rest ->
      match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2
      | Success t2 c2 r2 -> 
        (suffix_transitivity r2 c2 rest c1 input;
        Success (f t1 t2) (c1+c2) r2)

let parse_comb_1e #a #b #c (prev_input:string)
  (x:parser_ctxe a prev_input) (f: a -> b -> Tot c) (y:parser_ctx b prev_input) 
  (input:string{strlen input <= strlen prev_input}) : Tot (parse_result c input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 c1 rest ->
      match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2
      | Success t2 c2 r2 -> 
        (suffix_transitivity r2 c2 rest c1 input;
        Success (f t1 t2) (c1+c2) r2)

// Second argument is an unconstrained parser
// But this doesn't allow us to loosen < to <=
let parse_comb2 #a #b #c (prev_input:string)
  (x:parser_ctx a prev_input) (f: a -> b -> Tot c) (y:parser b) 
  (input:string{strlen input < strlen prev_input}) : Tot (parse_result c input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 c1 rest ->
      match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2
      | Success t2 c2 r2 -> 
        (suffix_transitivity r2 c2 rest c1 input;
        Success (f t1 t2) (c1+c2) r2)

// Neither argument is unconstrained
let parse_comb #a #b #c (prev_input:string)
  (x:parser_ctx a prev_input) (f: a -> b -> Tot c) (y:parser_ctx b prev_input) 
  (input:string{strlen input < strlen prev_input}) : Tot (parse_result c input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success t1 c1 rest ->
      match (y rest) with
      | ParseError e2 a2 -> ParseError e2 a2
      | Success t2 c2 r2 -> 
        (suffix_transitivity r2 c2 rest c1 input;
        Success (f t1 t2) (c1+c2) r2)

(*
 handling literals
 *)

// This version takes a string, but we will need to prove that the string
// has nonzero length to use it (with another defintiion.)  
// Literals don't get that for free.
let literal (tok:string{0 < strlen tok}) (input:string) : Tot (parse_result (z:string{z=tok}) input) =   
  if strlen tok > strlen input then
     ParseError (sprintf "literal '%s'" tok) input
  else let m = sub input 0 (strlen tok) in
     if m = tok then
        Success m (strlen tok) (suffix_at input (strlen tok))
     else
        ParseError (sprintf "literal '%s'" tok) input

// This version takes a single character instead, so it can be used with a literal as-is.
let literal_char (tok:char) (input:string) : Tot (parse_result (z:string{z=string_of_list [tok]}) input) =   
  if 1 > strlen input then
     ParseError (sprintf "literal '%c'" tok) input
  else let m = FStar.List.Tot.hd (list_of_string input) in
     if m = tok then
        Success (string_of_list [tok]) 1 (suffix_at input 1)
     else
        ParseError (sprintf "literal '%c'" tok) input

// Return the value inside of the given brackets
let brackets #a (orig_input:string) 
  (lbracket:string{strlen lbracket > 0}) (x:parser_ctx a orig_input) (rbracket:string{strlen rbracket >0}) 
  (input:string{strlen input <= strlen orig_input}) : Tot (parse_result a input) =
  parse_comb1
    orig_input  // context
    (literal lbracket) // first parser
    (fun t1 t2 -> t2 )   // transformation: take second result        
    (parse_comb2        // second parser
        orig_input            // same context?
        x                     // parser in argument
        (fun t2 t3 -> t2 )      // transformation: take result of x
        (literal rbracket))
    input

let brackets_char #a (orig_input:string) 
  (lbracket:char) (x:parser_ctx a orig_input) (rbracket:char) 
  (input:string{strlen input <= strlen orig_input}) : Tot (parse_result a input) =
  parse_comb1
    orig_input  // context
    (literal_char lbracket) // first parser
    (fun t1 t2 -> t2 )   // transformation: take second result
    (parse_comb        // second parser
        orig_input            // same context?
        x                     // parser in argument
        (fun t2 t3 -> t2 )      // transformation: take result of x
        (literal_char rbracket))
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

let parse_apply_ctxe #a #b (ctx:string) (f:a->b) (x:(parser_ctxe a ctx)) 
  (input:string{strlen input <= strlen ctx}) 
  : Tot (parse_result b input) =
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
// FIXME: this is not very good, it only shows the location of the top-level "either" clause 
// when both parts fail.
let or_of_reasons #a #i (r1:string) (r2:string) (at:string) 
  :  (r:(parse_result a i){ParseError? r}) =
  ParseError (concat " or " [r1; r2]) at
    
// Parse one of two options of the same type. Does not indicate which was chosen,
// you'll have to have the value indicate that.
let parse_either #a (x:parser a) (y:parser a) (input:string) : Tot (parse_result a input) =
  match (x input) with
  | Success t1 c1 rest -> Success t1 c1 rest
  | ParseError e1 a1 -> match (y input) with
     | Success t2 c2 r2 -> Success t2 c2 r2 
     | ParseError e2 a2 -> or_of_reasons e1 e2 input

let parse_either_ctx #a (ctx:string) (x:parser_ctxe a ctx) (y:parser_ctxe a ctx) (input:string{strlen input <= strlen ctx}) : Tot (parse_result a input) =
  match (x input) with
  | Success t1 c1 rest -> Success t1 c1 rest
  | ParseError e1 a1 -> match (y input) with
     | Success t2 c2 r2 -> Success t2 c2 r2 
     | ParseError e2 a2 -> or_of_reasons e1 e2 input

// Parse an entire list of the same type
let rec parse_alternatives_ctx #a (ctx:string) (x:list(parser_ctxe a ctx){Cons? x}) (input:string{strlen input <= strlen ctx}) : Tot (parse_result a input) =
  match x with
  | hd :: [] -> (hd input)
  | hd :: tl -> (parse_either_ctx ctx hd (parse_alternatives_ctx ctx tl) input) 

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

(* Parse optional and repeated types *)

(*
// The Kleene star won't terminate if the parser doesn't consume input.  So, we'll
// enforce totality by exiting as soon as it doesn't. 
let rec parse_star_aux #a (input:string) (x:parser a) (prev_a:list a) : Tot (parse_result (list a) input) (decreases (strlen input)) =
  match (x input) with
  | ParseError _ at -> 
     ParseError "inner parser failed" input
  | Success v rest -> 
     if rest = input then 
       Success 
     
     ((List.Tot.rev prev_a),input)
       else ( suffix_is_shorter rest input;
              // suffix_is_substring rest input;
              // proper_substring rest input;
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

*)

let rec parse_plus_aux #a (orig_input:string) (x:parser a) 
 (prev:(list a){Cons? prev}) (consumed:nat{consumed>0}) (rest:string{is_suffix_at rest orig_input consumed}) 
: Tot (parse_result (z:(list a){Cons? z}) orig_input) (decreases (strlen rest)) =
  match (x rest) with
  | ParseError e1 a1 -> Success prev consumed rest
  | Success new_elt c1 r1 ->
   ( suffix_transitivity r1 c1 rest consumed orig_input;
     parse_plus_aux 
       orig_input
       x
       (List.Tot.append prev [new_elt]) // TODO: build, then reverse?
       (consumed + c1)
       r1 )

// Parse one or more of the given parser, returned as a list
let parse_plus #a (x:(parser a)) (input:string) : Tot (parse_result (z:(list a){Cons? z}) input) =
  match (x input) with
  | ParseError e1 a1 -> ParseError e1 a1
  | Success first_elt c1 r1 ->
    parse_plus_aux input x [first_elt] c1 r1
     

// Parse zero or one of the given parser, returned as an option
// Must be followed by another parser that consumes input in order to succeed.
// TODO: multiple options
let parse_option #a #b (x:(parser a)) (y:(parser b)) (input:string) 
: Tot ((parse_result (option a) input)*(parse_result b input)) =
  match (x input) with
  | Success v1 c1 r1 -> 
     ( match (y r1) with
       | Success v2 c2 r2 -> 
           suffix_transitivity r2 c2 r1 c1 input; 
           (Success (Some v1) c1 r1, Success v2 (c1+c2) r2)
       | ParseError e2 a2 -> (ParseError e2 a2, ParseError e2 a2)
     )
  | ParseError e1 a2 ->
     ( match (y input) with
       | Success v2 c2 r2 -> (Success None c2 r2, Success v2 c2 r2)
       | ParseError e2 a2 -> (ParseError e1 a2, ParseError e2 a2)
     )

let parse_option_ctx2 #a #b (ctx:string) (x:(parser a)) (y:(parser_ctx b ctx)) 
  (input:string{strlen input < strlen ctx})
: Tot ((parse_result (option a) input)*(parse_result b input)) =
  match (x input) with
  | Success v1 c1 r1 -> 
     ( match (y r1) with
       | Success v2 c2 r2 -> 
           suffix_transitivity r2 c2 r1 c1 input; 
           (Success (Some v1) c1 r1, Success v2 (c1+c2) r2)
       | ParseError e2 a2 -> (ParseError e2 a2, ParseError e2 a2)
     )
  | ParseError e1 a2 ->
     ( match (y input) with
       | Success v2 c2 r2 -> (Success None c2 r2, Success v2 c2 r2)
       | ParseError e2 a2 -> (ParseError e1 a2, ParseError e2 a2)
     )

type digit_string = (x:string{x = "0" \/ x = "1" \/ x = "2" \/ x = "3" \/ x = "4" \/ x = "5" \/ x = "6" \/ x = "7" \/ x = "8" \/ x = "9"})

// This definition fails if one of the possibilities is missing!
// ... or out of order.  Exciting!
let digit : (parser digit_string) =
    parse_rename "digit" (literal_char '0' <|> literal_char '1' <|> literal_char '2' <|> literal_char '3' <|> literal_char '4' <|> literal_char '5' <|> literal_char '6' <|> literal_char '7' <|> literal_char '8' <|> literal_char '9')

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

let parse_apply_opt #a #b #c (x:parser a) (y:parser b) (f:(option a)->b->c) (input:string) : (parse_result c input) =
   let pr = parse_option x y input in
       match pr with 
       | (Success v1 _ _, Success v2 c2 r2) -> Success (f v1 v2) c2 r2
       | (_, ParseError a2 e2) -> ParseError a2 e2
   

// Parse a signed decimal (only - is recognized, not +)
let signed_integer : parser int = 
    parse_rename "integer"
      (parse_apply_opt           
           (parse_forget (literal_char '-'))
           unsigned_integer
           (fun (sign:option string) (v:int) -> 
             match sign with 
             | Some _ -> op_Multiply (-1) v
             | None -> v
             ))

// Consume any space and go on to the next parser
// TODO: work on any whitespace characters
let space #a (x:parser a) (input:string) : (parse_result a input) =
    snd (parse_option (parse_plus (literal_char ' ')) x input)

let space_ctx #a (ctx:string) (x:parser_ctx a ctx) 
    (input:string{strlen input < strlen ctx}) 
   : (parse_result a input) =
    snd (parse_option_ctx2 ctx (parse_plus (literal_char ' ')) x input)


(*
  Binary operator helper
*)

// This operator is allowed to recurse on the right only
let binop_char_ctx #a #b #c  (ctx:string) 
  (left:parser a) (binop:parser string) (right:parser_ctx b ctx) 
  (comb:a -> b -> c)
  (input:string{strlen input <= strlen ctx}) : Tot (parse_result c input) =  
  parse_comb1
    ctx  // context
    left
    comb   // transformation: combine with post-operator result
    (parse_comb1
        ctx            // same context?
        binop
        (fun t2 t3 -> t3 )       // transformation: take result of right
        right)
    input

let binop_char_ctxe #a #b #c  (ctx:string) 
  (left:parser_ctxe a ctx) (binop:parser string) (right:parser_ctx b ctx) 
  (comb:a -> b -> c)
  (input:string{strlen input <= strlen ctx}) : Tot (parse_result c input) =  
  parse_comb_1e
    ctx  // context
    left
    comb   // transformation: combine with post-operator result
    (parse_comb1
        ctx            // same context?
        binop
        (fun t2 t3 -> t3 )       // transformation: take result of right
        right)
    input



