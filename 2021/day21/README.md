# Day 21 solution notes

Part 1 was a fairly simple "simulation" and almost felt like object-oriented programming.  The only major hurdle was
that I accidentally used `n=1 /\ n=2` to define turns instead of `n=1 \/ n=2`, and so things trivially type-checked
until I fixed that.

The termination condition on `play_until_target_score` is a hack; it should be possible to do better.  (The requirement
is to ensure it's always a natural number, so 2020 should be enough but *proving* it's enough seems a little difficult?)

For Part 2, I didn't believe that recursing through the tree of possibilities would scale.  This was incorrect, but it
led me to over-engineer the problem.  Instead, I built a vector of all possible game states.  Then I calculated the
predecessors of each game state, and added them up to produce the next time's vector.  Writing the predecessor function
was error-prone; this was an area where if I had been able to write the spec, it could have helped a lot.

As a result, the solution runs fairly slowly.  (Even without dumping the entire vector, which I did for debugging.)

I attempted to write `mapi_init` in tail-recursive form, but that actually seemed to run slower.

## F* successes

I was eventually able to run Part 2; the performance was certainly better than if it didn't compile to a real programming
language.  :)

## F* problems

There were lots of things that I felt were Python one-liners that were very had to write in F*.

When a condition cannot be satisfied, F* will verify any function depending on such condition as having the correct type.  So when I had
the wrong definition of `turn`, `player_1_move` and `player_2_move` type-checked even with obvious errors.  I understand logically
why this is the case, but from a programming point of view maybe a warning would be appropriate?

I would *really* like to have proved that `from_index` and `to_index` were inverses, but the math was just too hard. It seems
like I would need very large expressions as arguments of the various `Math.Lemmas` covering division.  I rewrote `to_index` to
its current form because I thought that would be easier to work with, but maybe `to_index` needs to be rewritten too.

F*'s documentation on `List.Tot.mapi_init` was subtly wrong.  (https://github.com/FStarLang/FStar/pull/2413)  The
documentation on `List.Tot.mapi` was correct but very confusing, so I thought it was wrong.

More substantially, `FStar.List.Tot.mapi` does not prove that its integer argument is in-bounds (it's not even a `nat`!)  Nor is
there a lemma that the resulting list is the correct length.  The version I included does both.

I ran into difficulties again with the inferred types not being specific enough to `fold_left`.  This caused a lot of
head-scratching about where it needed to be fixed: in the lambda?  In an argument?  Eventually I gave `nat` explicitly
as the first implicit argument to `fold_left`.

It is really starting to feel as if F* actively discourages use of higher-level functions--- or at least that its standard library
does handle dependent types well.

## Questions

What is the appropriate model for proving the correctness of `predecessor_states_1`?  How difficult is it?

Why can't Z3 automatically handle lemmas like this one? Its ability to handle integer division seems very poor.

```FStar
let cancel_mul_div2 (a:nat) (n:nat{n>0}) (b:nat{b<n}): Lemma (((op_Multiply a n) + b) / n = a) = 
  Math.Lemmas.lemma_div_plus b a n;
  Math.Lemmas.small_div b n
```

