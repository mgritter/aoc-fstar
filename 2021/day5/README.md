# Day 5 solution notes

I made the input easier to parse by replacing the arrow ` -> ` with just a comma.  Then I could
re-use the comma-separated list parser from day 4.

I was flummoxed that `FStar.Set.set` has no way to measure its cardinality. That was my plan (from experience with
Python sets) to count the number of unique instances.  So I hacked in a last-minute addition of an extra list
to keep count.

Things I would have liked to do, but seemed to hard:
  * The type `points_on_two_lines` doesn't really do what it says.  There's no condition for the two lines being different lines.  But, it seems like we would be a map of points to lines in order to prove that this was the case, so I didn't try.
  * Similarly, the intent is that the list we are using (to count the cardinality) contains exactly those elements which are in the set.  But how can we express that?  We'd need to re-type the list every time we added an element to say "all the old elements are still in the list."  Maybe some helper function could be defined.  Maybe doing it reverse would be easier (this set is all members of the list.)
  * For part 2, my `point_on_line` type allows any point in the bounding box defined by (x1,y1) through (x2,y2).  It would be nice to be more specific.

## F* successes

No deep problems proving things tonight.  It handled type-checking `points_on_horizontal_line` and `points_on_vertical_line` very well, as well as
the complicated set types.

## F* problems

Underpowered `set` abstraction; seems not oriented toward programmatic use.  Computationally these are quite useful in Python, and since I don't trust that `FStar.Map` is constant-time time I really
was hoping to use more `set`s for future problems.  Some options below in the questions.

I tried using a dependent tuple, which turned out to be the wrong thing.  (See above, trying to get "this list consists entirely of members of the set".)  This syntax is not really documented
in the tutorials or wiki.  I eventually figured out it is `(| x, y |)`.

## Questions

How to guarantee everything in the set of points has two *distinct* lines?

How much can I abstract "parse all the lines" for future use?

How to express the diagonal "between" case properly?  Should the slope or delta be part of the line type?

Should I write my own set type?  Or just write an extra accessor that calls `BatSet.cardinal`.  (Really, we could use a `map` for sets too, or at least the ability
to turn them back into lists.)
