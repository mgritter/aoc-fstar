module Covariance

val x : list nat
let x = [1; 2; 3]

val y : list int
[@@expect_failure]
let y = x

val a : option (n:int{n % 2 = 0})
let a = Some 4

val b : option int
[@@expect_failure]
let b = a

// See 
// https://github.com/FStarLang/FStar/issues/65
// for a lengthy discussions of what would be required
// to make this work in F*
