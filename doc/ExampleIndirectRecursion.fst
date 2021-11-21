module ExampleIndirectRecursion

// Calculate 
// a(n) = (1 + a(n-1))^2

val a : n:nat -> Tot nat
val plus_one_squared : n:nat{n>0} ->  f:(x:nat{x<<n} -> Tot nat) -> Tot nat 

let plus_one_squared n f =
  let fn = f (n - 1) in
     op_Multiply (1+fn) (1+fn)

let rec a n =
  if n = 0 then 1 else plus_one_squared n a


