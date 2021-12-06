# Day 6 solution notes

I was pretty sure that in part 2 we were going to be asked to go for a much longer
number of days, so it was prety easy to write part 1 with an eye towards going more than 80 days,
by keeping a vector of counts of fish, rather than a list of fish. So, both parts are in Part1.fst today.

The hard part, suprisingly, was "modify just one element of the list"!  (And prove that it
remains the same length).  I thought that this would be straightforward once I found `split3`
in the standard library, but it was not.

## F* successes

The standard library's `fold_left_monoid` lemma was just what I needed for a proof (not directly
related to solving the problem.)  I used it incorrectly for a while, but that's on me.

## F* problems

I continue to have trouble because + takes integers, so when used on `nat`s the result is not
an integer by default: we have to prove it each time.  So this file has `nat_add` to encapsulate
that, but it's pretty annoying.

This lemma was surpisingly hard to prove:

```FStar
let split3_recombine (l:list nat) (i:nat{i<length l}) (replacement:nat) 
                     (before:list nat) (orig:nat) (after:list nat)
 : Lemma (requires split3 l i = (before, orig, after) )
         (ensures length (before  @ [replacement] @ after) = length l)
```

I had to add a `lemma_splitAt_fst_length` to mirror the `lemma_splitAt_snd_length` that's
in the standard library.  The first seems an odd omission?  (See below; I was looking in the
wrong place.)

## Questions

Would I have been better off using `FStar.Map` when parsing the list of fish, so I could do an update?  I am somewhat
dubious. I don't trust `FStar.Map` because the lookup appears linear-time in the number of updates!

I found other lemmas about `split3` in `FStar.List.Pure.Properties.fst`, including the one I needed:

```FStar
let lemma_split3_length (#t:Type) (l:list t) (n:nat{n < length l}) :
  Lemma
    (requires True)
    (ensures (
        let a, b, c = split3 l n in
        length a = n /\ length c = length l - n - 1)) =
  splitAt_length n l
```

I hadn't thought that maybe I should import both `List.Tot` and `List.Pure`; this seems like bad library
design.  Why are lemmas about a function defined in `FStar.List.Tot.Base` be under `Pure`?
