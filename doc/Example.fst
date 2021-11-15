module Example

open FStar.Mul
open FStar.Tactics

// Original proof

val factorial: x:nat -> Tot int
let rec factorial n = 
  if n = 0 then 1 else n * (factorial (n - 1))

let rec factorial_is_positive x : Lemma(factorial x > 0) =
  match x with
  | 0 -> ()
  | _ -> factorial_is_positive (x - 1)

// Example of apply_lemma: just call a previous lemma that matches the goal

let appeal_to_lemma () : Tac unit =
  dump "before";
  apply_lemma (`factorial_is_positive);
  dump "after"

let factorial_is_positive2 x = 
  assert( factorial x > 0) by appeal_to_lemma()

// Example of including the lemma in the tactic

let appeal_to_new_lemma () : Tac unit =
  dump "before";
  let rec temporary_lemma (y:nat) : Lemma(factorial(y) > 0) = 
     if y = 0 then ()
     else temporary_lemma (y-1) in
    apply_lemma (quote temporary_lemma);
    dump "after"

let factorial_is_positive3 (x:nat) = 
  assert (factorial x > 0) by appeal_to_new_lemma()

// Proof of specific cases using the inductive step

let factorial_step (x:nat{x>0}) 
 : Lemma (requires (factorial (x-1) > 0))
         (ensures (factorial x > 0))
     = ()
 
let rec constant_depth (depth:nat) : Tac unit =
  if depth = 0 then 
     dump "depth 0"
  else
     (
     apply_lemma (`factorial_step);
     dump "after lemma";
     constant_depth (depth - 1)
     )
     
let factorial_is_positive4 = 
  assert (factorial 5 > 0) by (constant_depth 5)

(*
// What if we apply it only once?

let single_step (n:nat) : Tac unit =
   cases_bool (quote (n > 0));
   dump "after cases";
   let _ = implies_intro() in
     dump "after implies";
     apply_lemma (`factorial_step);
     dump "after lemma"

let factorial_is_positive5 (n:nat{n<2}) = 
  assert (factorial n > 0) by single_step n
*)

