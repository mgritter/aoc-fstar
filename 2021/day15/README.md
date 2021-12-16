# Day 15 solution nodes

I spent some time thinking about whether it was feasible to solve this
in some less-than-efficient manner that would be easier to implement.  While
I didn't anticipate that part 2 would increase the matrix size by 5x, I did
see that the input for part 1 was already large.

So, I knew I wanted to use Dijkstra's, but that may have been a mistake---
BFS might have been easier.  I first tried to create a heap using a tree
structure, but I gave up on that when the the rebalancing step on
removal was too hard to picture.  (Probably using an imperative implementation
would be feasible.)  So I looked up a functional priority queue structure
and implemented it: leftist heaps.

This priority queue doesn't have a "decrease-node" implementation because
there's no way to find a node.  So, I resigned myself to the same node
appearing in the priority queue up to four times, and we just don't
re-enqueue nodes that are `Finished`.

## F* successes

I was happy that `merge_heaps` type-checked correctly on my first try,
but it did contain a bug-- one that my type doesn't catch.  I wrote a unit
test to catch it, but wonder how I could have done better.

## F* problems

Not having a priority queue or other suitable data structure is a big
negative.  I anticipated this might be a problem, but hadn't finished
converting the red-black tree in the examples directory to hold payloads.

The `expand_matrix` function does not reliably type-check with the standard
amount of time, and I had to spell out some extra types.

I don't entirely understand when `dfst`/`dsnd` are necessary.  It seems like
the first parameter of a dependent pair can sometimes be used to fill in
an implicit argument?

I used an `assume` because the relationship between the queue and the
distance matrix could not be easily proved.

## Questions

How can we prove the correctness of Dijkstra's algorithm?  
