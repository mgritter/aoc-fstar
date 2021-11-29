module ExampleState

open FStar.IO
open FStar.ST
open FStar.Printf
open FStar.All

val x : ref int
let x = alloc 0

val y : ref int
let y = alloc 0

val head : ref int
let head = alloc 0

let f n : St unit =
    x := (!x + n)

let doit _ : ML unit = 
 f 5;
 f 10;
 print_string (sprintf "%d\n" (!x))

let _ = doit()



  
