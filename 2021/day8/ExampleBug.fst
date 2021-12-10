module ExampleBug

open FStar.List.Tot

val x:list nat
let x = [1;2;3;4;1]

let count_1 (prev_total:nat) (l:list nat) : nat = prev_total + (count 1 x)

val count: #a:eqtype -> a -> list a -> Tot nat
let rec count #a x = function
  | [] -> 0
  | hd::tl -> if x=hd then 1 + count x tl else count x tl

     
