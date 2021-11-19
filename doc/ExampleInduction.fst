module ExampleInduction

open FStar.Mul
open FStar.Tactics

(*
Show use of tactics to prove an assertion via induction.
*)

// Example functions we might want to prove things about
val factorial: nat -> Tot int
let rec factorial n = 
  if n = 0 then 1 else n * (factorial (n - 1))

let rec sum_of_squares (x:nat) : Tot int =
  if x = 0 then 0 else (x * x) + (sum_of_squares (x-1) )
  
// Our super-powerful metatheorem about induction on natural numbers.
let rec nat_induction (p : nat -> Type) (n:nat)
  : Lemma (requires p 0 /\ (forall (x:nat) . ( x > 0 /\ p (x-1) ) ==> p x ))
    (ensures p n)
  = if n = 0 then () else nat_induction p (n-1)

// Unwrap a term that has been squashed
// Perhaps we could just use (unsquash (pack t))?
let access_type_in_squash (t:typ) : Tac term =
  match inspect t with 
  | Tv_App hd a -> 
    begin
    match inspect hd with
    | Tv_FVar f ->
       if inspect_fv f = squash_qn then
          fst a
       else
          fail "Not a squash type"
    | _ -> fail "Not a squash type"
    end
  | _ -> fail "Not a squash type"

// Check that there is just one binder in the current
// environment, and reutrn it.
let induction_binder () : Tac binder =
  match cur_binders() with
  | [] -> fail "No variable in environment"
  | hd :: [] -> hd
  | hd :: tl -> fail "More than one variable in environment"

// Paste together the current binder and the current (unsquashed) goal
// to get the abstraction we need to use `nat_induction`.
// Frankly, I am not sure how we got away with this; not recommended for production use.
let nat_induction_tac () : Tac unit =
     let term_to_prove = access_type_in_squash (cur_goal()) in (
       print ("goal type = " ^ term_to_string( term_to_prove ) );
       let binder = induction_binder() in
         print ("binder = " ^ binder_to_string( binder) );
           let myProp = mk_abs [binder] term_to_prove in
             let l = mk_e_app (`nat_induction) [myProp] in
               print( "my_lemma = " ^ term_to_string( l ) );
               dump "before";
               apply_lemma l;
               dump "after lemma";
               split();
               dump "after split"
     )

let factorial_is_positive (n:nat) = 
  assert (factorial n > 0) by nat_induction_tac()

let factorial_is_greater_than_arg (n:nat) = 
  assert (factorial n >= n) by nat_induction_tac()

let sum_of_squares_formula (m:nat) = 
  assert (sum_of_squares m = (2*m+1)*m*(m+1)/6) by nat_induction_tac()

(*
Notes on failed approaches:

We can't drop an antiquote in the middle of Lemma(), there's a check in the grammar that specifically prohibits that.
We also can't put it in GTot(u:unit{...}).

But, confusingly, the return type of a letrec is not part of the view?

Computation types are part of sgelts view, but it looks like we can only introduce those if building a plugin?

Can we define a type instead?  Not clear how to add type annotations, do they desugar to something?
i.e., (let type = <blah> in let rec foo (x:nat) (Lemma type) = ... )
*)
