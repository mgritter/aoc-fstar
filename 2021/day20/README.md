# Day 20 solution notes

MOAR CELLULAR AUTOMATA!

I was once again able to re-use chunks of code from my warm-up problem.

I looked at the input right away and noticed that index 0 was '#' (and, come to think of it,
I just *assumed* that index 511 was '.') so that the empty squares would flip every time.
I handled this by adding a variable that tracks the "default" state of the border, so that
it was not fixed.

The table lookup posed an interesting challenge: I could re-use the binary to integer conversion
I had already written, but I needed to prove that a 9-bit input resulted in an index no longer than 511.
I spent a bunch of time writing a function that returned the correct bound, and then I had
the wrong binary value -- oops.

The other design decision is whether to represent the CA as a matrix at all, or use a sparse representation.
I don't think the sparse representation would scale very well; the input looked dense.

## F* successes

The `expand_matrix` function has a nice type, although I wish I would have been able to describe
its operation in a proof-- it turns out that it had two different bugs!

Running the large matrix was still plenty performant in the generated OCaml code.

I learned that F* *does* come with a power function, and indeed a specialized `pow2` function-- and moreover that
it is in prims.fst so it's automatically loaded!  So I was able to write `input_length_x` as a lemma without
using normalizaton or repeating a single-step lemma nine times or something gross like that.

## F* problems

Who knew that pow2 existed?  What else is waiting to be found?

Standard frustrations with using refined types-- count_pixels didn't work until I explicitly
assigned some types to the lambdas.  It complained that it couldn't turn a `matrix` into
a `(list (list cell))`, because the inner list in a matrix has a refined type.

## Questions

What is an appropriate model for the matrix transition function?  How can we prove its
correctness, in some way simpler than re-implementing it?
Is it something like `forall x y : old pos = transition new_pos`, i.e,
an order-independent description of what it does?
