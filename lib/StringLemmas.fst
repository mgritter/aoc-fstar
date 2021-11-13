module StringLemmas

open FStar.String
open FStar.List.Tot
open FStar.Classical
open FStar.Squash
open FStar.Tactics
  
// This property is used for partially unpacking the existential definition of is_substring
let is_substring_at (a:string) (b:string) (i : nat): prop = 
  exists (n:nat). i + n <= strlen b /\ (sub b i n) == a 

// Subtyping relationship
let prefix_is_substring (a:string) (b:string) :
  Lemma (requires (is_prefix a b))
        (ensures (is_substring a b)) =
        ()
(*
    exists_intro
     (fun (p:(nat*nat){fst p + snd p <= strlen b}) -> (fst p) + (snd p) <= strlen b /\ (sub b (fst p) (snd p)) == a )
     (0,strlen(a))
*)

let suffix_is_substring (a:string) (b:string) :
  Lemma (requires (is_suffix a b))
        (ensures (is_substring a b)) =
        ()

(* Lemmas about sub-lists *)

// First n elmements of a list
let rec first_n #a (n:nat) (l:(list a){length l >= n}) : (x:(list a){length x = n}) =
  if n = 0 then []
  else match l with
  | hd :: tl -> hd :: (first_n (n-1) tl)

// Sublist of a list starting at i and taking j elements
let rec sublist #a (i:nat) (n:nat) (l:(list a){length l >= i+n}) : (x:(list a){length x = n}) =
  if n = 0 then []
  else if i > 0 then match l with
  | hd :: tl -> (sublist (i-1) n tl)
  else match l with
  | hd :: tl -> hd :: (sublist 0 (n-1) tl)

// Taking the entire sublist gives an equal string
let rec sublist_of_whole_length #a (l:(list a)) : 
  Lemma (ensures (sublist 0 (length l) l) == l )
  = match l with 
   | [] -> ()
   | hd ::tl -> sublist_of_whole_length tl

// Taking a prefix of a prefix gives the shorter prefix
let rec prefix_of_prefix_of_sublist #a (l:(list a)) (x:nat{length l >= x}) (y:nat{y <= x}) 
 : Lemma (ensures (sublist 0 y l) == (sublist 0 y (sublist 0 x l)))
  = if y = 0 then ()
    else match l with
    hd :: tl -> prefix_of_prefix_of_sublist tl (x-1) (y-1)

// Taking a sublist of the sublist gives a particular sublist
let rec sublist_of_sublist_is_sublist #a (l:(list a)) 
   (p1:nat) (n1:nat{p1+n1 <= length l})  // a sublist
   (p2:nat) (n2:nat{p2+n2 <= n1})        // a sublist of that
 : Lemma (ensures (sublist p2 n2 (sublist p1 n1 l)) 
                == (sublist (p1+p2) n2 l))
  = if p1 = 0 then
      if p2 = 0 then
         prefix_of_prefix_of_sublist l n1 n2
      else
         match l with
           hd :: tl -> sublist_of_sublist_is_sublist tl 0 (n1-1) (p2-1) n2
    else match l with
      hd :: tl -> sublist_of_sublist_is_sublist tl (p1-1) n1 p2 n2


// String lemmas: have to admit this definition because no model exists, and 
// standard library lemmas are not strong enough; they don't state anything
// about sub.
// This is my attempt to define sub in terms of things that *are* strong enough
// to reason about.
let substring_is_sublist (s:string) (i:nat) (l:nat{i+l <= strlen s}) : 
  Lemma (ensures (sub s i l) =
                 (string_of_list (sublist i l (list_of_string s))))
     = admit()

// Derived lemmas
let all_strings_of_length_zero_are_equal (s:string{strlen s=0}) (t:string{strlen t=0}) 
  : Lemma (ensures (s=t)) = 
    // assert( list_of_string s = [] );
    // assert( list_of_string t = [] );
    string_of_list_of_string s;
    string_of_list_of_string t

let substring_of_length_is_equal (s:string)
 : Lemma (ensures (sub s 0 (strlen s)) == s )
   = substring_is_sublist s 0 (strlen s);
     sublist_of_whole_length (list_of_string s);
     // assert( sublist 0 (strlen s) (list_of_string s) = (list_of_string s) );
     string_of_list_of_string s

let prefix_is_reflexive (s:string)
 : Lemma (ensures is_prefix s s)
   = substring_of_length_is_equal s

let suffix_is_reflexive (s:string)
 : Lemma (ensures is_suffix s s)
   = substring_of_length_is_equal s

let substring_is_reflexive (s:string)
 : Lemma (ensures is_substring s s)
   = substring_of_length_is_equal s

let prefix_is_shorter (a:string) (b:string) 
 : Lemma (requires (is_prefix a b))
         (ensures (strlen a) <= (strlen b) )
   = ()

let suffix_is_shorter (a:string) (b:string) 
 : Lemma (requires (is_suffix a b))
         (ensures (strlen a) <= (strlen b) )
   = ()

let substring_is_shorter (a:string) (b:string) 
 : Lemma (requires (is_substring a b))
         (ensures (strlen a) <= (strlen b) )
   = ()

let substring_of_substring_is_substring (s:string) 
   (p1:nat) (n1:nat{p1+n1 <= strlen s}) 
   (p2:nat) (n2:nat{p2+n2 <= n1})
 : Lemma (ensures (sub s (p1+p2) n2) == (sub (sub s p1 n1) p2 n2))
 = sublist_of_sublist_is_sublist (list_of_string s) p1 n1 p2 n2;
   //     (sublist (p1+p2) n2 (list_of_string s))
   // ==  (sublist p2 n2 (sublist p1 n1 (list_of_string s)))
   // therefore equality still holds when we wrap with s_o_l
   //     (s_o_l (sublist (p1+p2) n2 (list_of_string s)))
   // ==  (s_o_l (sublist p2 n2 (sublist p1 n1 (list_of_string s))))
   // The left side is (sub s (p1+p2) n2)
   substring_is_sublist s (p1+p2) n2;
   assert( (sub s (p1+p2) n2) == string_of_list (sublist p2 n2 (sublist p1 n1 (list_of_string s))));
   // To simplify the right hand side we need to inject a l_o_s/s_o_l pair
   // in front of (sublist p1 n1 ...)
   list_of_string_of_list (sublist p1 n1 (list_of_string s));
   // Then simplify to (sub s (p1+p2) n2 ) == (sub XXXXXXX p2 n2)   
   substring_is_sublist (string_of_list (sublist p1 n1 (list_of_string s))) p2 n2;
   substring_is_sublist s p1 n1

let prefix_of_prefix_is_prefix (s:string) (x:nat{strlen s >= x}) (y:nat{y <= x})
 : Lemma (ensures (sub s 0 y) == (sub (sub s 0 x) 0 y))
 = substring_of_substring_is_substring s 0 x 0 y

let suffix_of_suffix_is_suffix (s:string) (x:nat{strlen s >= x}) (y:nat{y <= x})
 : Lemma (ensures (suffix s y) == (suffix (suffix s x) y))
 = substring_of_substring_is_substring s (strlen s - x) x (x-y) y

// Lemma: a prefix of a prefix is a prefix
let prefix_transitivity (a:string) (b:string) (c:string) :
  Lemma (requires (is_prefix a b) /\ (is_prefix b c))
        (ensures (is_prefix a c)) 
       // (sub c 0 (strlen b)) = b
       // (sub b 0 (strlen a)) = a     
       // WTP: (sub c 0 (strlen a)) = a
     = prefix_is_shorter a b;  // (strlen a) <= (strlen b)
       prefix_of_prefix_is_prefix c (strlen b) (strlen a)

let suffix_transitivity (a:string) (b:string) (c:string) :
  Lemma (requires (is_suffix a b) /\ (is_suffix b c))
        (ensures (is_suffix a c)) 
     = suffix_is_shorter a b;
       suffix_of_suffix_is_suffix c (strlen b) (strlen a)

// OK, there's got to be a better way to do this
// Extract all the values that ensure a subtring b and b substring c, then
// use our super lemma above.
let substring_transitivity (a:string) (b:string) (c:string) :
  Lemma (requires (is_substring a b) /\ (is_substring b c))
        (ensures (is_substring a c)) 
     = exists_elim 
        // goal 
        (is_substring a c)
        // get the pair implied by (is_substring b c)
        (Squash.get_proof (is_substring b c))
        // derivation
        (fun p1 -> exists_elim 
           (is_substring a c)  // same goal
           (Squash.get_proof (is_substring_at b c p1))
           (fun n1 -> exists_elim
             (is_substring a c)
             (Squash.get_proof (is_substring a b))
             (fun p2 -> exists_elim
                (is_substring a c)
                (Squash.get_proof (is_substring_at a b p2))
                (fun n2 ->
                   substring_of_substring_is_substring c p1 n1 p2 n2;
                   exists_intro
                      (fun (p:(nat*nat){fst p + snd p <= strlen c}) -> (fst p) + (snd p) <= strlen c /\ (sub c (fst p) (snd p)) == a )
                      (p1+p2,n2)))))


// Lemma if a and b are the same length, then if a is a substring of b,
// they must be equal.
let substring_equality (a:string) (b:string) :
  Lemma (requires (is_substring a b) /\ (strlen a) = (strlen b))
        (ensures (a=b))
   = if strlen a = 0 then
     all_strings_of_length_zero_are_equal a b
   else
     assert (sub b 0 (strlen a) = a);
     substring_of_length_is_equal b

// Lemma: if x is a substring of y, and x != y, then strlen x < strlen y
let proper_substring (a:string) (b:string)
: Lemma ( requires (is_substring a b) /\ (a <> b) )
  ( ensures (strlen a) < (strlen b)) = 
  substring_is_shorter a b;
  // Convert substring_equality into an implication, so we can apply modus tollens
  move_requires_2 substring_equality a b


