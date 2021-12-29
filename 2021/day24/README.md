# Day 24 solution notes

I decided I wanted to take a decompilation or symbolic execution approach,
even though it was probably not the most efficient.  The advantage is
that I could more easily prove correctness of each reduction, and avoid
doing brute-force search.  Which I hoped would be useful for part 2.

Eventually I realized that what I wanted was to build a tree of conditionals
which would allow case-by-case analysis.  So the symbolic execution attempt
to preserve a "normal form" which consists of `IfEqThen` operations
with non-conditional expressions at the leaves, and no conditionals
appearing in the values being tested for equality.

The final piece was writing two cases to eliminate impossible conditions, which dramatically
reduced the number of possibilities: down to 1!

```
(+ i_2 -1 )  == i_3  /\
(+ i_4 5 )  == i_5  /\
(+ i_6 8 )  == i_7  /\
(+ i_1 4 )  == i_8  /\
(+ (% (+ i_0 7 ) 26 ) -4 )  == i_9  /\
(+ i_11 -6 )  == i_12  /\
(+ (% (+ i_10 12 ) 26 ) -10 )  == i_13 
```

That meant I didn't have to write the code to numerically compare different possibilities.
(I went back and did this last step only after previous output showed a lot of conditions
that were impossible.)

I successfully proved all the transformations correct!

I did not do the same for the search procedure.  I eventually just resorted to
brute-force search because layering an SMT solver on top of F* was not something I wanted
to do.  :)  But, it would be nice to see what sort of thing we could do to make
the solver more efficient.

## F* successes

Pattern matching FTW.

I couldn't prove a + (b % m) = (a+b) %m because it wasn't true!  Oops.

Similarly, I couldn't prove that my bounds check for the case of `(+ (% (+ i_a k) 26) y) == i_b` was
correct, because it had a bug! I thought it was just a problem of not having the modulus lemmas.

## F* problems

Can't match on a negative integer, because it's not treated as a literal
by the parser: https://github.com/FStarLang/FStar/issues/2415

It sure would be nice if the F* standard library had ways to print lists by default.

## Questions

I was only able to prove `push_op_correctness` for `AddOp`.  Taking a general function of type
`expr->expr->expr` seems very hard to reason about.  I tried writing a condition I thought would
be sufficient but the same problem occurred.  I don't know what the correct type to use here is;
can we define a sufficiently well-behaved condition that all the constructors have?
