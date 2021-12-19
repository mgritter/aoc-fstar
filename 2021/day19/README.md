# Day 19 solution notes

The major obstacle to getting this problem correct for me was 3-D rotation, so I made my mistakes early.  :(

I thought about trying to prove the rotation functions correct, but it was not at all clear to me I was capable
of coming up with a better model.

My search algorithm was:
1. For each unplaced scanner U,
2. Loop over all the placed scanners P,
3. Loop over all 24 orientations of U,
4. Loop over all U's beacons B1
5. Loop over all P's beacons B2,
6. Assume B1 == B2 and compute the offset from that
7. Does that produce 12 matches?  If so, place U.

This has a significant inefficiency; once we consider a (U,P) pair we should not do so again later.  The answer
will not change.

## FStar successes

I was able to define refined types for `scanner` that helped check each function had its arguments in the
correct place, and that progress was being made.

Wrote higher-order function `try_alternatives` that worked well.

## FStar problems

`FStar.Set.as_set` doesn't compile.

The type ascription was necessary in this piece of code
```FStar
                parse_beacons ((({
                   x=index csv 0;
                   y=index csv 1;
                   z=index csv 2
                }) <: beacon) :: prev)
```
because otherwise `{x=...;y=...;z=...}` was interpreted as an incomplete `pos_and_dir`.  I can see that
it's ambiguous, but the type should be quite clear from context.

F* needs the equivalent of Python itertools.  :)

## Questions

What's the best model for verifying the spatial orientation functions?
