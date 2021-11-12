module StringLemmas

open FStar.String
open FStar.List.Tot
open FStar.Classical
     
// Need to define substrings to state that the parser consumes
// a portion of the input and leaves the rest.
let is_substring (a:string) (b:string) : bool = 
  if strlen a = 0 then true else
  if strlen a > strlen b then false else
  (sub b 0 (strlen a)) = a

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

// Taking a sublist of a sublist gives the shorter sublist
let rec sublist_of_sublist_is_sublist #a (l:(list a)) (x:nat{length l >= x}) (y:nat{y <= x}) 
 : Lemma (ensures (sublist 0 y l) == (sublist 0 y (sublist 0 x l)))
  = if y = 0 then ()
    else match l with
    hd :: tl -> sublist_of_sublist_is_sublist tl (x-1) (y-1)
    
// String lemmas: have to admit because no model exists, and 
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
 : Lemma (ensures (sub s 0 (strlen s)) = s )
   = substring_is_sublist s 0 (strlen s);
     sublist_of_whole_length (list_of_string s);
     // assert( sublist 0 (strlen s) (list_of_string s) = (list_of_string s) );
     string_of_list_of_string s

let substring_is_reflexive (s:string)
 : Lemma (ensures is_substring s s)
   = substring_of_length_is_equal s

let substring_is_shorter (a:string) (b:string) 
 : Lemma (requires (is_substring a b))
         (ensures (strlen a) <= (strlen b) )
   = ()

let substring_of_substring_is_substring (s:string) (x:nat{strlen s >= x}) (y:nat{y <= x})
 : Lemma (ensures (sub s 0 y) == (sub (sub s 0 x) 0 y))
 = sublist_of_sublist_is_sublist (list_of_string s) x y;
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
   
// Lemma: a substring of a substring is a substring
let substring_transitivity (a:string) (b:string) (c:string) :
  Lemma (requires (is_substring a b) /\ (is_substring b c))
        (ensures (is_substring a c)) 
       // (sub c 0 (strlen b)) = b
       // (sub b 0 (strlen a)) = a     
       // WTP: (sub c 0 (strlen a)) = a
     = substring_is_shorter a b;  // (strlen a) <= (strlen b)
       substring_of_substring_is_substring c (strlen b) (strlen a)
       
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


