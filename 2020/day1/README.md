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

The initial version constructed a new list by filtering elements from
`input` that were not in `input_set`, thereby proving they were all
`valid_int`s.

The new version has a much longer proof that this obvious fact is true.  It
proceeds via two lemmas, both proven by recursion on lists:

1. If all elements of L are members of S, and Super is a superset of S, then
   all elements of L are members of Super too.
2. All elements of L are members of the set constructed by `as_set L`

We need to use lemma 1 again to reach the final conclusion, using set equality
to imply the subset relationship.

### Abusing the solver

It seems like we ought to be able to just feed the whole problem to Z3. If instead of a list, the input was a huge type

```
x:int{x == 1735 /\ x == 1700 /\ x == 1358 ...}
``` 

would that work?  Would code that _converted_ the list to a type work?
Why or why not?
