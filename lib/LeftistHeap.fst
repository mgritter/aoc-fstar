module LeftistHeap

// Leftist heap, following
// https://courses.cs.washington.edu/courses/cse326/08sp/lectures/05-leftist-heaps.pdf

type int_1 = (z:int{z >= -1})

noeq type heapnode : v:Type -> (npl:int_1) -> Type =
  | Null : #v:Type -> heapnode v (-1)
  | Node: #v:Type -> 
          npl_left:int_1 -> left:heapnode v npl_left -> 
          key:nat -> value:v -> 
          (npl_right:int_1{npl_right <= npl_left}) -> right:(heapnode v npl_right) -> 
          heapnode v (1 + (min npl_left npl_right))

let empty_heap (#v:Type) = Null

let singleton_heap (#v:Type) (key:nat) (value:v) : (heapnode v 0) =
  Node (-1) Null key value (-1) Null

// We don't have any way to decrease_key for this heap implementation.
// So, we will have to allow the same value to be inserted multiple times,
// and just check in our matrix whether we've already found the minimum value for it.

// Merge two leftist heaps
let rec merge_heaps (#v:Type) (#npl_a:int_1) (a:heapnode v npl_a) (#npl_b:int_1) (b:heapnode v npl_b) 
  : Tot (npl_result:int_1 & (heapnode v npl_result)) 
    (decreases %[a;b]) =
  if Null? a then
     (| npl_b, b |)
  else if Null? b then
     (| npl_a, a |)
  else if Node?.key a <= Node?.key b then (
     // a has the minimum key
     let new_left = Node?.left a in
     let npl_left = Node?.npl_left a in
     let new_tree = merge_heaps (Node?.right a) b in
     let npl_right = dfst new_tree in
     let new_right = dsnd new_tree in
        if npl_right <= npl_left then
           // Order is OK
           (| 1 + (min npl_left npl_right),
              Node npl_left new_left 
                   (Node?.key a) (Node?.value a)
                   npl_right new_right |)
        else
           // Invariant not OK, swap the trees to preserve it
           (| 1 + (min npl_left npl_right),
              Node npl_right new_right 
                   (Node?.key a) (Node?.value a)
                   npl_left new_left |)                      
  ) else 
     // b has the minimum key
     let new_left = Node?.left b in
     let npl_left = Node?.npl_left b in
     let new_tree = merge_heaps a (Node?.right b) in
     let npl_right = dfst new_tree in
     let new_right = dsnd new_tree in
        if npl_right <= npl_left then
           // Order is OK
           (| 1 + (min npl_left npl_right),
              Node npl_left new_left 
                   (Node?.key b) (Node?.value b)
                   npl_right new_right |)
        else
           // Invariant not OK, swap the trees to preserve it
           (| 1 + (min npl_left npl_right),
              Node npl_right new_right 
                   (Node?.key b) (Node?.value b)
                   npl_left new_left |)                      

let insert (#v:Type) (#npl_root:int_1) (root:heapnode v npl_root) (key:nat) (value:v) 
  : Tot (npl_result:int_1 & (heapnode v npl_result)) =
  merge_heaps root (singleton_heap key value)

noeq type pop_result : v:Type -> Type =
  | MinValue : (#v:Type) -> (key:nat) -> (value:v) -> (npl:int_1) -> (new_root:heapnode v npl) -> pop_result v
  
let pop_min (#v:Type) (#npl_root:int_1{npl_root >= 0}) (root:heapnode v npl_root)
 : Tot (pop_result v) =
 match root with 
 | Node npl_left left key value npl_right right ->
   let new_tree = merge_heaps left right in
     MinValue key value (dfst new_tree) (dsnd new_tree)
