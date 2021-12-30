module FinSet

open FStar.BV
module L = FStar.List.Tot

// Computable sets on 0, 1, ..., N-1.
// Maybe some utilities to give those elements other representations


type finite_set (n:pos) = bv_t n

let bvweight (#n:pos) (v:bv_t n) : nat =
  L.count true (bv2list v)

let cardinality #n(s:finite_set n) : nat =
  bvweight s

let rec list_of_aux (n:pos) (i:nat{i<=n}) (l:(list bool){i + L.length l = n}) : 
  Tot (r:(list (e:nat{e < n})){L.length r = L.count true l})
      (decreases l) = 
   match l with
   | [] -> []
   | hd :: tl -> if hd then
       i :: (list_of_aux n (i+1) tl)
     else
       list_of_aux n (i+1) tl

let list_of #n (s:finite_set n) : (l:(list (e:nat{e < n})){L.length l = cardinality s}) = 
   list_of_aux n 0 (bv2list s)

let union (#n:pos) (s1:finite_set n) (s2:finite_set n) : Tot (finite_set n) =
  bvor s1 s2

let intersection (#n:pos) (s1:finite_set n) (s2:finite_set n) : Tot (finite_set n) =
  bvand s1 s2

let mem (#n:pos) (i:nat{i<n}) (s:finite_set n) =
  


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
