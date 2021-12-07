# Solution notes

For part 1 I thought about the problem a bit and concluded the optimal point
was the median.  My reasoning was:
 * If we're to the right of the median, we can move left and
   decrease a lot of crabs by 1, and an equal or less number increase by 1.
 * If we're to the left of the median, we can move right and etc.
 * Therefore, the median must be an optimal solution.

Implementing this turned out to require proving that "sorting the list does
not change its length" but that turned out to not be something I could
derive from the standard library lemmas.

I tried to prove that the median is correct in Part1, after my solution
was accepted, but I could not finish the proof in F*.

For Part 2, I just did brute force search.  I didn't even write the
tail-recursive version.

## F* successes1

I was glad to have `sortWith` available.

I had this lemma backwards, so of course it did not type-check, but
I was pleased that simple induction works once I got it right:

```FStar
let rec summed_distance_to_neighbor_plus (l:list int) (meeting:int) :
  Lemma (ensures (summed_distance_to l (meeting+1)) = 
                 (summed_distance_to l meeting) +
                 (num_lte l meeting) - (num_gt l meeting )) =
  match l with 
  | [] -> ()
  | hd::tl -> 
     summed_distance_to_neighbor_plus tl meeting
```

## F* problems

The obstacle to writing `median` was proving that the offset
`length sorted / 2` (or `length l / 2`) was in bounds.  I was surprised that
I was not able to derive the fact that the sorted length is equal to the
unsorted length from the standard library.

It is implied by this lemma:
```FStar
val sortWith_permutation: #a:eqtype -> f:(a -> a -> Tot int) -> l:list a ->
  Lemma (requires True)
        (ensures (forall x. count x l = count x (sortWith f l)))
        (decreases (length l))
```
but only if we have a "these are all the unique elements in the list" to
work with, or some theorem about summing over the `forall`.  Similarly,
showing that all elements are present and that the result is sorted
does not guarantee that we didn't remove any elements!

```FStar
val sortWith_sorted: #a:eqtype -> f:(a -> a -> Tot int) -> l:list a ->
  Lemma (requires (total_order #a (bool_of_compare f)))
        (ensures ((sorted (bool_of_compare f) (sortWith f l)) /\ (forall x. mem x l = mem x (sortWith f l))))
        (decreases (length l))
```

## Proving that the median is optimal

I feel like these two lemmas are on the right track: they show what
happens to the sum as we move "meeting" around.

```FStar
let rec summed_distance_to_neighbor_plus (l:list int) (meeting:int) :
  Lemma (ensures (summed_distance_to l (meeting+1)) = 
                 (summed_distance_to l meeting) +
                 (num_lte l meeting) - (num_gt l meeting )) =
  match l with 
  | [] -> ()
  | hd::tl -> 
     summed_distance_to_neighbor_plus tl meeting

let rec summed_distance_to_neighbor_minus (l:list int) (meeting:int) :
  Lemma (ensures (summed_distance_to l (meeting-1)) = 
                 (summed_distance_to l meeting) -
                 (num_lt l meeting) + (num_gte l meeting )) =
  match l with 
  | [] -> ()
  | hd::tl -> 
     summed_distance_to_neighbor_minus tl meeting
```

But I couldn't figure out how to apply them, so maybe that's the wrong
starting point.  I think one idea is to iterate these into a "cost function"
and say:
  * If we have a point where num_lt and num_gt are equal, then
    moving away from that point can only increase the cost.
  * The median is such a point.

The problem is the median, as defined, does not actually balance num_lt and
num_gt, they can be off by one.  Would fixing this simplify the proof?
(We'd have to leave the integers, so I don't think it would.)

I was trying to prove that the median is special that way, but I don't
have a clear picture about how to show that the median (almost-) balances
the number of items above and below it.

## Proving that part 2 is optimal

Is there a better formulation for part 2?

Could we at least prove that the optimal lies within the range
I defined to search?
