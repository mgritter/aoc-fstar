# Day 12 solution notes

I spent a little time looking for a non-brute-force solution but I didn't see one.  Multiplying the adjacency matrix is the wrong thing,
even without additional complications.

Fortunately, my part 1 was easy to modify to solve part 2; I justed added another parameter to keep track of the little cave we had
visited twice.

https://adventofcode.com/2021/day/12

I wrote using the `Dv` effect because the algorithm as written might never terminate if there is a cycle of "big" caves.  In `Part2.fst`,
after solving the problem, I did write a `Tot`-effect version that works by bounding the path length; we could simply use a very large
value when processing the input.  It does not seem possible to write a `Lemma` about a function that has the `Dv` effect. 

## F* successes

Even though `Map.t` has a linear-time implementation, the solution was fast.

## F* problems

Given the argument
```FStar
(visited:Set.set (s:string{is_little s}))
```
It seems like the check here:
```FStar
else if ( is_little curr && Set.mem curr visited ) then
```
is a little bit redundant.  Yes, `Set.mem` only takes the refined type. But trivially, anything not of that type can't be in the set anyway!
Is this redundancy necessary for correctness, or an artifact of how `Set` is implemented, or just a simplification in the definition?

## Questions

Does the `Dv` effect prohibit the use of a function in a precondition or postcondition?  It looks like it,
the functions that manipulate properties are defined as having GTot effect.

Can we prove properties about (the total version) of count_paths successfully?  I saw too many pieces to
try to do it on-stream: we need to be able to do induction on the size of the set.  But we don't have a cardinality
function!  So we would have to do it on lists, and I wrote a lemma to get started in that direction.

Could we make a version of `Set` that guranteed all its members were of a certain type, but performed membership 
on the supertype anyway?  If the type-check was expensive, it would be nice to avoid it when redundant.  On the other hand,
being able to express that property on updates is very valuable, so dropping to `Set string` seems the wrong direction.
