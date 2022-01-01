module FinSet

open FStar.Tactics
module L = FStar.List.Tot

// Computable sets on 0, 1, ..., N-1.
// Maybe some utilities to give those elements other representations
// These are represented as (sorted) lists to make it easier to reason about!
// In the future they could be represented by bitvectors instead, but
// bv_t lacks an easy membership operator.

let rec members_are_unique (#a:eqtype) (l:list a) : Tot bool =
  match l with 
  | [] -> true
  | hd :: tl -> if L.mem hd tl then false else
      members_are_unique tl

type finite_set (n:pos) = (l:(list (e:nat{e<n})){members_are_unique l})

let cardinality #n (s:finite_set n) : nat = L.length s

let list_of #n (s:finite_set n) : (l:(list (e:nat{e < n})){L.length l = cardinality s}) = 
   s

let mem #n (i:nat{i<n}) (s:finite_set n) =
  L.mem i s

let unique_not_in_tail (#a:eqtype) (l:list a) (e:a) : 
  Lemma (requires (members_are_unique l /\ ~ (L.mem e l)))
        (ensures (members_are_unique (e :: l)))
        = ()

let rec union #n (s1:finite_set n) (s2:finite_set n) : 
  Tot (u:(finite_set n){forall (x:nat{x<n}) . mem x u <==> ( mem x s1 \/ mem x s2 )}) =
  match s1 with
  | [] -> s2
  | hd :: tl -> let u = union tl s2 in
    if mem hd u then u else hd :: u
    
let rec intersection #n (s1:finite_set n) (s2:finite_set n) : 
  Tot (u:(finite_set n){forall (x:nat{x<n}) . mem x u <==> ( mem x s1 /\ mem x s2 )}) =
  match s1 with
  | [] -> []
  | hd :: tl -> let rest = intersection tl s2 in
    if mem hd s2 then hd :: rest else rest

let rec difference #n (s1:finite_set n) (s2:finite_set n) : 
  Tot (u:(finite_set n){forall (x:nat{x<n}) . mem x u <==> ( mem x s1 /\ ~(mem x s2) )}) =
  match s1 with
  | [] -> []
  | hd :: tl -> let rest = difference tl s2 in
    if mem hd s2 then rest else hd :: rest

let rec universe_aux (n:pos) (i:pos{i<=n}) :
  Tot (u:(finite_set n){(forall x . (mem x u <==> x < i))}) 
      (decreases i) =
  if i = 1 then 
    let (z:finite_set n) = [0] in
      assert (forall (x:nat{x<1}) . mem x z);
      z
  else
    (i-1) :: ( universe_aux n (i-1))

let universe (n:pos) :
  Tot (u:(finite_set n){forall (x:nat{x<n}) . mem x u}) =
  universe_aux n n

let complement #n (s1:finite_set n) :
  Tot (u:(finite_set n){forall (x:nat{x<n}) . mem x u <==> ~ (mem x s1)}) =
  difference (universe n) s1



