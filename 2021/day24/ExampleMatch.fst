module ExampleMatch

let sign = (z:int{z = 0 \/ z = (-1) \/ z = 1})

(* Syntax error

let example_1 (s:sign) : string =
 match s with
 | (-1) -> "negative"
 | 1 -> "positive"
 | 0 -> "zero"
*)

// No syntax erorr, but doesn't work!
// neg1 is treated as binding, not a match with the previous value.
let example_2 (s:sign) : string =
 let neg1 = (-1) in
 match s with
 | neg1 -> "negative"
 | 1 -> "positive"
 | 0 -> "zero"

let _ = assert( example_2 (-1) = "negative" )
let _ = assert( example_2 0 = "negative" )   // oops

[@@expect_failure]
let _ = assert( example_2 0 = "zero" )
[@@expect_failure]
let _ = assert( example_2 1 = "positive" )

// Working version, but fragile
let example_3 (s:sign) : string =
 match s with
 | v when v = (-1) -> "negative"
 | 1 -> "positive"
 | 0 -> "zero"

let _ = assert( example_3 (-1) = "negative" )
let _ = assert( example_3 0 = "zero" )

// Fails with "When clauses are not yet supported in --verify mode"
[@@expect_failure]
let example_4 (s:option sign) : string = 
  match s with
  | None -> "unknown"
  | Some v when v = (-1) -> "negative"
  | Some 1 -> "positive"
  | Some 0 -> "negative"
  
  
  
