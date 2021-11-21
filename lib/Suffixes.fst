module Suffixes

open FStar.String
open FStar.List.Tot
open FStar.Tactics
     
(* This is an adaptation of StringLemmas, oriented around proving thing about the following 
 * proper suffix relation, which we'll use for parsing.
 *)
  
let is_suffix_at (a:string) (b:string) (n:nat{n>0}) : bool = 
  if n + strlen a <> strlen b then false else
  (sub b n (strlen a)) = a

let suffix_at (b:string) (n:nat{0 < n /\ n <= strlen b}) : (x:string{is_suffix_at x b n}) =
  (sub b n (strlen b - n))

(*
 * We introduce a lemma about `sub` that is missing from the standard library, in terms
 * of sublists (which we _can_ reason about.)
 *)

// Sublist of a list starting at i and taking j elements
let rec sublist #a (i:nat) (n:nat) (l:(list a){length l >= i+n}) : (x:(list a){length x = n}) =
  if n = 0 then []
  else if i > 0 then match l with
  | hd :: tl -> (sublist (i-1) n tl)
  else match l with
  | hd :: tl -> hd :: (sublist 0 (n-1) tl)

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

let substring_is_sublist (s:string) (i:nat) (l:nat{i+l <= strlen s}) : 
  Lemma (ensures (sub s i l) =
                 (string_of_list (sublist i l (list_of_string s))))
     = admit()


(* 
 * Now we can prove the "main theorem" about how substrings nest.
 *)
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

(*
 * Facts about is_suffix_at are now simple corrolaries
 *)
 let suffix_is_shorter (a:string) (b:string) (p:nat{0<p})
 : Lemma (requires (is_suffix_at a b p))
         (ensures (strlen a) + p = (strlen b) )
   = ()

let suffix_transitivity (a:string) (p1:nat{0<p1}) (b:string) (p2:nat{0<p2}) (c:string)
 : Lemma (requires (is_suffix_at a b p1) /\ (is_suffix_at b c p2))
         (ensures (is_suffix_at a c (p1+p2))) 
 = substring_of_substring_is_substring c p2 (strlen b) p1 (strlen a)

