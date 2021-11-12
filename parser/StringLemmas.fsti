module StringLemmas

open FStar.String

val is_substring (a:string) (b:string) : bool

// If two strings have zero length, they are equal.
val all_strings_of_length_zero_are_equal (s:string{strlen s=0}) (t:string{strlen t=0}) 
 : Lemma (ensures (s=t))

// A substring of the same length as the original, is the original
val substring_of_length_is_equal (s:string) 
 : Lemma (ensures (sub s 0 (strlen s)) = s )

// All strings are substrings of themeselves
val substring_is_reflexive (s:string)
 : Lemma (ensures is_substring s s)

// The substring relationship imposes an order on string length
val substring_is_shorter (a:string) (b:string) 
 : Lemma (requires (is_substring a b))
         (ensures (strlen a) <= (strlen b) )

// Taking a shorter substring of a longer substring gives the shorter substring
val substring_of_substring_is_substring (s:string) (x:nat{strlen s >= x}) (y:nat{y <= x})
 : Lemma (ensures (sub s 0 y) == (sub (sub s 0 x) 0 y))

// is_substring is a transitive relationship
val substring_transitivity (a:string) (b:string) (c:string)
 : Lemma (requires (is_substring a b) /\ (is_substring b c))
         (ensures (is_substring a c)) 

// If a and b are the same length, and a is a substring of b,
// they must be equal.
val substring_equality (a:string) (b:string) :
  Lemma (requires (is_substring a b) /\ (strlen a) = (strlen b))
        (ensures (a=b))

// If x is a substring of y, and x != y, then strlen x < strlen y
val proper_substring (a:string) (b:string)
 : Lemma (requires (is_substring a b) /\ (a <> b))
         (ensures (strlen a) < (strlen b))
         
