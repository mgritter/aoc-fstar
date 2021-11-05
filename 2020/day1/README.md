## Day 1 solution notes

I skipped figuring out parsing for day 1 and just included the input as
a single list.

The part 1 solution is inefficient but easily converted to the part 2 solution.

### F* successes

Type-checking failed when I accidentally entered 
```
  let z = 2020 - x + hd in
```
instead of
```
  let z = 2020 - x - hd in
```

in part 2.

### Problems encountered with F*

Syntax: can you do

```
type soln_pair = p:valid_int * valid_int{fst p + snd p = 2020}
```

all on one line?  How?

Why is there no `print_int`?  `print_all` just showed garbage when I used it
on the tuple.

### Proving that the list contains only elements of the set created from it

I have no idea how to make this work.  I'm not even sure how we would express
a lemma about the type of a variable that's already bound.

My guess is that we could simultaneously create the set and a copy of the
list, recursively. I think we'd first have to prove that

```
list x:{mem x subset} => list x:{mem x superset}
```

I'm not even sure if => is right, how do we prove one type is a subset
of another type?

I thought about asserting that the membership check always succeeds.

### Abusing the solver

It seems like we ought to be able to just feed the whole problem to Z3. If instead of a list, the input was a huge type

```
x:int{x == 1735 /\ x == 1700 /\ x == 1358 ...}
``` 

would that work?  Would code that _converted_ the list to a type work?
Why or why not?
