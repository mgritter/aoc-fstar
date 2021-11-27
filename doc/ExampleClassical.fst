module ExampleClassical

open FStar.Classical
open FStar.Classical.Sugar
open FStar.IndefiniteDescription
open FStar.Tactics
open FStar.Squash

// My answer to a forum question about proving
// Lemma ((forall x. exists b. p x b) ==> (exists f. forall x. p x (f x)))

// FStar.Classical has exists_intro but only for Tot functions.
let exists_intro_gtot (#a: Type) (p: (a -> GTot Type)) (witness: a)
    : Lemma (requires (p witness)) (ensures (exists (x: a). p x))
    = ()

let exists_intro_gtot_squash (#a: Type) (p: (a -> GTot Type)) (witness:a{p witness})
    : GTot (squash (exists (x: a). p x))
    = exists_intro_gtot p witness;
      FStar.Squash.get_proof (exists (x: a). p x)
    
// This is the function that, given an A, returns the B
let get_ghost_value_from_exists #a #b 
 (p : a -> b -> prop) 
 (_ : squash (forall (x:a) . exists (y:b) . p x y))  
 (some_a:a)
 : GTot (y:b{p some_a y})  =
  // forall elimination, not necessary to be explicit
  assert( exists (y:b) . (p some_a y) );  
  let f (x:b) : (t:prop{exists (y:b) . p some_a y}) = (p some_a x) in 
    FStar.IndefiniteDescription.indefinite_description_ghost b f

// Is there an easier way to go directly from the above to the lemma?
// Without working with squashed types explicitly?
let forall_exists_swap #a #b 
  (p : a -> b -> prop) 
  (pre:squash (forall (x:a). exists (y:b). p x y)) 
  : GTot (squash  (exists (f:a->GTot b). forall x. p x (f x))) =
    let condition_on_f (f:a -> GTot b) : GTot prop = (squash (forall (z:a) . (p z (f z )))) in
      exists_intro_gtot_squash 
        #(f: a -> GTot b)
        condition_on_f
        (get_ghost_value_from_exists p pre)

let forall_exists_swap_lemma #a #b (p : a -> b -> prop) 
  : Lemma (requires (forall (x:a). exists (y:b). p x y))
          (ensures  (exists (f:a->GTot b). forall x. p x (f x))) =
      FStar.Squash.give_proof
        (forall_exists_swap p (FStar.Squash.get_proof (forall (x:a). exists (y:b). p x y)))
