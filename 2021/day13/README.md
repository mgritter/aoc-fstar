# Day 13 solution notes

A few seconds' thought convinced me I did *not* want to use a matrix today. Applying the fold operation to
each point in a list was straightforward, and deduplicating only added a little bit of complexity.

I didn't parse the folding instructions, but instead represented them as code.  This led to a copying error,
but was probably still faster than parsing them.  :)

In Part1.fst I was able to prove that the fold operation preserves distance from the fold axis.  (I did it
only for X-axis folds, but the same proofs should work for Y-axis folds.)

In Part2.fst I was able to prove that the fold_points function does deduplicate its output.  Unfortunately,
I did not find `no_repeats` until well into my proof, so I didn't go back and try to use that instead
of the property I used.  Amusingly, the correctness of part 2 today does *not* depend on deduplication
working correctly!  Only part 1 does-- the matrix printer I wrote doesn't care how many times a point is represented.

## F* successes

No real difficulty in implementation today, and I was able to write the folding lemma right away.

I like representing the inputs as a list of functions to apply; that's almost like having a DSL.

## F* problems

While my deuplication proof did not end up super-complicated, they were still hard to find "what's the missing piece"
in each proof.  In one case it turned out that `mem_count` is not included by pattern-- it seems hard to predict
what gets a pattern and what does not, without knowing the library very well.

I got an unusual warning:
```
(Warning 290) SMT may not be able to prove the types of folds at <input>(61,23-61,28) (Prims.list (_: Part1.point -> Prims.Tot Part1.point)) and
folds at <input>(61,23-61,28) (Prims.list (_: Part1.point -> Prims.Tot Part1.point)) to be equal, if the proof fails, try annotating these with the same type
```
Those look like exactly the same input ranges to me...?  I think the root cause is that functional equality is iffy but this seems like an easy case
(and type-checking did not, in fact, fail.)

## Questions

Is this split into `folded_points_respects_visited` and `folded_points_are_deduplicated` necessary?
Or is that just that I didn't have an adequate plan for the proof and `repsects_visited` is a detour?
I *think* it is necessary to describe the difference between "the element is known to belong to the set" and
"the element might not belong to the set".

What's an example of the failure the warning talks about?
