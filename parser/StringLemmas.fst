module StringLemmas

open FStar.String
open FStar.List.Tot
open FStar.Classical
     
// Need to define prefixes to state that the parser consumes
// a portion of the input and leaves the rest.
let is_prefix (a:string) (b:string) : bool = 
  if strlen a > strlen b then false else
  (sub b 0 (strlen a)) = a

let is_suffix (a:string) (b:string) : bool = 
  if strlen a > strlen b then false else
  (sub b (strlen b - strlen a) (strlen a)) = a

let is_substring (a:string) (b:string) : prop = 
  exists (i:nat) (n:nat{n+i <=strlen b}) . (sub b i n) == a 

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

let prefix_is_substring (a:string) (b:string) 
  : Lemma (requires (is_prefix a b))
          (ensures (is_substring a b))
  = ()

let suffix_is_substring (a:string) (b:string) 
  : Lemma (requires (is_suffix a b))
          (ensures (is_substring a b))
  = ()

// Derived lemmas
let all_strings_of_length_zero_are_equal (s:string{strlen s=0}) (t:string{strlen t=0}) 
  : Lemma (ensures (s=t)) = 
    // assert( list_of_string s = [] );
    // assert( list_of_string t = [] );
    string_of_list_of_string s;
    string_of_list_of_string t

let substring_of_length_is_equal (s:string)
 : Lemma (ensures (sub s 0 (strlen s)) = s )
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

let prefix_of_prefix_is_prefix (s:string) (x:nat{strlen s >= x}) (y:nat{y <= x})
 : Lemma (ensures (sub s 0 y) == (sub (sub s 0 x) 0 y))
 = sublist_of_sublist_is_sublist (list_of_string s) 0 x 0 y;
   //     (sublist 0 y (list_of_string s))
   // ==  (sublist 0 y (sublist 0 x (list_of_string s)))
   // therefore 
   //     (s_o_l (sublist 0 y (list_of_string s)))
   // ==  (s_o_l (sublist 0 y (sublist 0 x (list_of_string s))))
   substring_is_sublist s 0 y;
   // therefore
   assert( (sub s 0 y) == string_of_list (sublist 0 y (sublist 0 x (list_of_string s))));
   // To simplify the right hand side we need to inject a l_o_s/s_o_l pair
   // in front of (sublist 0 x ...)
   list_of_string_of_list (sublist 0 x (list_of_string s));
   // Then simplify to (sub s 0 y) == (sub XXXXXXX o y)
   substring_is_sublist (string_of_list (sublist 0 x (list_of_string s))) 0 y;
   substring_is_sublist s 0 x

// TODO: prove via duality instead?
// Same plan as above
let suffix_of_suffix_is_suffix (s:string) (x:nat{strlen s >= x}) (y:nat{y <= x})
 : Lemma (ensures (suffix s y) == (suffix (suffix s x) y))
 = sublist_of_sublist_is_sublist (list_of_string s) (strlen s - x) x (x - y) y;
   substring_is_sublist s (strlen s - x + x - y) y;
   assert( (sub s (strlen s - y) y) == string_of_list (sublist (x-y) y (sublist (strlen s - x) x (list_of_string s))));
   list_of_string_of_list (sublist (strlen s - x) x (list_of_string s));
   substring_is_sublist (string_of_list (sublist (strlen s - x) x (list_of_string s))) (x-y) y;
   substring_is_sublist s (strlen s - x) x

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

let substring_transitivity (a:string) (b:string) (c:string) :
  Lemma (requires (is_substring a b) /\ (is_substring b c))
        (ensures (is_substring a c)) 
  = admit()
// TODO

       
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


