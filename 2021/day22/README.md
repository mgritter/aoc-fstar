# Day 22 solution notes

I had a bad feeling that we were going to have to handle much larger
ranges, but in part 1 I couldn't think through what that might be.  I was
anticipating some sort of geometric decomposition, which would be hard
to implement.
(There *were* things that my solution would have been good at, but not
the entire volume.)

So for part 1 I felt it was better to iterate over (points * rules) rather
than updating a large 3x3 matrix.  Same number of points, but less work
per point, potentially?

The algorithm for part 2 is due to
https://gist.github.com/gnarf/15b67a343300d8c66cdd8d8ef4637bf2
who helpfully popped up in my Twitter feed just as I was feeling a bit lost.
The idea here is that we already know how to
compute what's lit for a stack of size N.  We can use that to compute
what's list for a stack of size N+1 by trimming to just the intersections
with the cuboid we're trying to add.

(Instead of doing inclusion-exclusion, which I contemplated several times.)

I wonder if the part 2 algorithm has an equally nice representation
working back-to-front instead of front-to-back in the rules?  I was
rather proud of the back-to-front version in part 1.

I spent a *long* time on part 2 with an off-by-one problem in my area
formula.  Worse, when I calculated it by hand I made the same mistake again!

I transformed the input so that it was just CSV instead of extra cruft
to work around.

## F* successes

I was able to write a *lot* of proofs while looking for my off-by-one bug.
The core part 2 algorithm was "tested" for 1 and 2 rule interactions.

Adding the correct constraints to `reboot_step` allowed F* to infer
a lot of things automatically, which gave me confident that `intersect_with`
was correct.

I was quite proud of getting the termination proof correct for the
part 2 algorithm:
```
let rec count_cubes (steps:list reboot_step) (prev_steps:list reboot_step) 
: Tot int
  (decreases %[(length steps + length prev_steps);(length steps)]) =
```

This lets us either decrease `steps` by one, or else recursively call
`count_cubes` with fewer total elements, but a longer `steps`.

## F* problems

I was not able to complete my proof of `intersect_lowers_area`.
I think this is something Z3 should be capable of, but I don't yet know
what the missing piece is.

I originally wrote:
```
let rec count_cubes (steps:list reboot_step) (prev_steps:list reboot_step) 
: Tot int
  (decreases %[(length steps + length prev_steps),(length steps)]) =
```
See the difference?  Neither did I, for a minute.  The problem is that it
has a comma rather than a semicolon.  I don't know what the comma
*means* in this context, but it is hardly ever correct.  I wish
there was a warning about it.

## Questions

Huge ambition: show that the point-by-point computation in part 1 and
the recursive formula in part 2 are equivalent!

How can we conclude the proof of `intersect_lowers_area`?  What is
missing, do we just need to do more basic steps?





