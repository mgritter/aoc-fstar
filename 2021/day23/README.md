# Day 23 solution notes

What a tough one!  I ended up with A* search, but it uses a *lot* of memory,
so the second part just barely completed.

A big improvement from part 1 to part 2 was deduplicating states, but that
unfortunately also costs memory.  Other improvements reduced the number
of states.

I think what I should have done is deduplicated while ignoring the
"visited" state, maybe I'll try that.

I thought of implementing "src,dest" pairs as the possible moves rather
than single steps, but I figured it would be roughly equivalent since
every step is a potential stopping point.

## F* successes

F* was able to alert me to several errors in pattern-matching.

I was able to re-use my leftist tree implementation.

## F* problems

It seemed hard to come up with a way to memoize the distances table;
I eventually arrived at a match-based solution that isn't *too* bad,
but very error-prone.

## Questions

As usual, what is the model of correctness here?

Is there a way to dramatically reduce memory usage?  (Besides something
like iterative deepening.)
