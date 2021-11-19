module ExampleLogic

open FStar.Mul

val factorial: n:nat -> Tot int
let rec factorial n = 
  if n = 0 then 1 else n * (factorial (n - 1))


// Write the inductive proof as a logical statement

// SMT can solve base case and inductive step
let _ = assert( forall (y:nat) . 
    ( ( y = 0 == true ) ==> (factorial 0 > 0 == true ) )
    /\
    ( ~(y = 0 == true) ==> (factorial (y-1) > 0 == true  ==> factorial y > 0 == true) ) )


// But fails on induction
[@@expect_failure]
let _ = assert ( 
    (  (factorial 0 > 0 == true )
        /\
        ( forall (y:nat) . ( (y > 0 == true) ==> (y -1 << y /\ (factorial (y-1) > 0 == true  ==> factorial y > 0 == true )))))
     ==>
    (forall (z:nat) . (factorial z > 0)))

[@@expect_failure]
let half_induction (n:nat) : Lemma
  (requires (n == 0) ==> (factorial 0 > 0 == true ) /\
            (n > 0 ) ==> (factorial (n-1) > 0 == true ==> factorial n > 0 == true))
  (ensures (factorial n > 0))
  = ()
  
let rec full_induction (n:nat) (p : nat -> prop) 
  : Lemma (requires p 0 /\ (forall (x:nat) . ( x > 0 /\ p (x-1) ) ==> p x ))
    (ensures p n)
  = if n = 0 then () else full_induction (n-1) p
