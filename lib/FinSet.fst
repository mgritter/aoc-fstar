module FinSet

open FStar.BV
module L = FStar.List.Tot

// This type allows you to specify the N elements that belong to the set.
// They are represented by a bitvector of that length, so that they have
// decidable equality.
type finite_set #a (n:pos) (univ:(list a){L.length univ = n}) = bv_t n

let bvweight (#n:pos) (v:bv_t n) : nat =
  L.count true (bv2list v)

let cardinality #a #n #univ (s:finite_set #a n univ) : nat =
  bvweight s

let cardinality_by_case #a (n:nat{n>1}) univ (s:finite_set #a n univ) :
  Lemma (requires (L.hd (bv2list s)) = true)
        (ensures cardinality #a #(n-1) #(L.tl univ) (list2bv (L.tl (bv2list s))) = 
                 cardinality s - 1) =
    assert( L.count true (L.tl (bv2list s)) =
            L.count true (bv2list s) - 1);
    admit()
 
let rec list_of_finite_set_aux #a #n #univ (s:finite_set #a n univ) : (l:(list a){L.length l = cardinality s}) =
  if n = 1 then
    let v = bv2list s in
      if L.hd v then (
         (L.hd univ) :: []
      ) else 
         []
  else (
    let v = bv2list s in
      if L.hd v then let rest = list_of_finite_set_aux #a #(n-1) #(L.tl univ) (list2bv (L.tl v)) in (
         assert( cardinality #a #(n-1) #(L.tl univ) (list2bv (L.tl v)) = cardinality s - 1);
         (L.hd univ) ::  rest
      ) else 
         list_of_finite_set_aux #a #(n-1) #(L.tl univ) (list2bv (L.tl v))
  )   

let list_of_finite_set #a #n #univ (s:finite_set a n univ) : (l:(list a){L.length l = cardinality s}) = 
  admit()

let bvhead (#n:pos) (v:bv_t n) : bool =
   hd (bv2list v)

let bvtail (#n:pos{n>1}) (v:bv_t n) : (bv_t (n-1)) =
   (list2bv (tl (bv2list v)))

let bvcons (#n:pos) (b:bool) (v:bv_t n) : (bv_t (n+1)) =   
   (list2bv (Cons b (bv2list v)))

let bvcons_ident (#n:pos{n>1}) (v:bv_t n) 
 : Lemma (ensures bvcons (bvhead v) (bvtail v) = v)
 = // (list2bv (Cons (bvhead v) (bvtail v)))
   // (list2bv (Cons (bvhead v) (bvtail v)))
   // (list2bv (Cons (hd (bv2list v) (bv2list (list2bv (tl (bv2list v)))))))
   list2bv_bij #(n-1) (tl (bv2list v));
   // (list2bv (Cons (hd (bv2list v) (tl (bv2list v)))))
   bv2list_bij v
