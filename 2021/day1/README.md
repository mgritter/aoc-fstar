# Day 1 solution notes

This was pretty straightforward list-handling. I used `snoc` (the opposite of `cons`) to ensure the rolling window was in the right order.

But, proving my solution correct escaped me.

### F* successes

It didn't find any errors tonight that I recall.

### F* problems

The large list literal caused problems; it takes about 5 seconds to type-check all by itself.

The solver could not determine that the length of the input literal was >= 3 in a timely fashion; it took 114 seconds to fail:

```
(Part2.fst(2039,2-2040,36))	Query-stats (Part2.part2, 1)	failed {reason-unknown=unknown because canceled} in 113688 milliseconds with fuel 2 and ifuel 1 and rlimit 2723280
```

I changed this to a run-time check instead.

I eventually figured out that there isn't a full set of lemmas for `snoc` in the standard library.  I used `lemma_snoc_length` to prove that
the length of the rolling window list is correct, but it doesn't have a SMTPat to include it automatically.  I had to write a new one
using `lemma_append_last` to prove the interaction of last and snoc.

### Questions

How can we prove the lemma `rolling_window_ok`?  Does it require double recursion on the list length and on the index?  At least I can write
what I think is the correct model to verify its correctness.

But, how can we prove `increase_count_aux` correct?  What is an appropriate model?



