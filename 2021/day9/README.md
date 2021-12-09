# Day 9 solution notes

Fortunately, I had my warmup exerise from 2020 so I could parse and iterate
over a matrix pretty quickly.  I was happy to use `List.Tot.collect`
for accumulating output in a way that both transformed and filtered the
data simultaneously.

For part 2, I eventually decided to use DFS, and it wasn't *too* painful,
although passing the map around in functional style might have been a mistake.
Given that I could not prove that DFS terminates without a lot more work,
I might as well have made it stateful?

It took me about 45 minutes to write the DFS, but it came out reasonably
clean.  I don't know what we could have done to prove its correctness?

## F* successes

As usual, it kept me honest on bounds-checking.

The use of `Set` was painless because I only needed to do membership checks,
not cardinality, and it appears to have compiled to efficient code.

## F* problems

Library design:
 * `List.Tot.index i l` returns the i'th element of the list `l`.
 * `List.index f l` returns the first element of `l` for which the function
`f` returns true.

These two functions should *not* have the same name.

## Questions

What would a proof of termination of DFS look like?  (Would we need
set cardinalities?)  What about correctness?
