# Day 18 solution notes

Both parts of the solution are in Part1.fst today.

Pattern-matching is usually a good choice for tree manipulation problems,
and it worked pretty well today. I made one error that needed to be debugged
when I returned a subtree instead of reconstructing a pair on success.
No special algorithmic insight was required, just careful implementation.

I got my best ranking so far, hit 2012 on the leaderboard for part 1.

I had to use the `Dv` effect because I cannot think of a metric that works
to prove reduction terminates.  Node count doesn't work, sum doesn't work (I think),
"error" count might stay the same...?

## F* successes

The type on `explode_number` proved that explosions cannot completely
escape, without any effort from me!  This removed a case from `reduce`.

```
let rec explode_number (x:number) (depth:nat) : (r:explode_result{LeftRight? r ==> depth >= 4}) =
```

## F* problems

Not having a `max` function in the standard library bit me again.  But
not too badly.

I tried to write `debug_add` like this:

```
let debug_add (s1:string) (s2:string) : ML unit = 
  let c1 = (list_of_string s1) in
  let c2 = (list_of_string s2) in
  let p1 : parse_result number c1 = parse_number c1 in
  let p2 : parse_result number c2 = parse_number c2 in
  match (p1,p2) with
  | (OK v1 _, OK v2 _) -> let debug_reduce v1 v2 in ()
  | _ -> print_string "parse error"
```

But the error messages from F* were incomprehensible.
```
(*?u126*) _ is not equal to the expected type _
```
or
```Expected type "parse_result number c1, parse_result number c2"; but "p1, p2" has type "(*?u452*) _ * (*?u453*) _"
```


## Questions

What is a metric that shows that the reduction process always terminates?

Is there a sensible spec for `reduce` or at least its component operations?
Or, at least, is there a way to use types to make sure that all the
complicated tree manipulation doesn't do something "silly"?
