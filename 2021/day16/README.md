# Day 16 solution notes

I had some experience implementing recursive-descent parsing in F* previously, but I adopted a simpler solution
here, where there are no parser combinators. Instead, the parsing is done by a single large function which
always decreases the size of the input, with a couple small exceptions and a couple helper functions.

Evaluation went pretty quickly, although the fact that I didn't more precisely define the allowable arguments
to GreaterThan, LessThan, and EqualTo meant that I could not prove anything about the evaluation function.

I had a parser error where I was throwing away the rest of the input. It would be nice to have a clean way to
express in each function what it consumed and what it threw away, as a type?

The binary-to-natural number conversion should ideally return a bound based on the size of the input list,
so that no extra check is needed.

## F* successes

The large recursive-descent parser type-checked with only minimal problems.

String concatenation allowed me to easily add more detailed error messages to find my parsing problem.

## F* problems

This function fails the termination checker:

```FStar
let rec sum_versions (msg:message) : Tot nat =
  match msg with 
  | Literal version value -> version
  | Operator version operands ->
     version + (List.Tot.fold_left (fun (t:nat) m -> t + (sum_versions m)) 0 operands)
```

It should be that `operands << m`, but I'm not sure whether that carries through so that the
individual elements are also `<< m`?  Or is that information just lost going through
`fold_left`?  Changing the function parameter to `(m:message{m << msg})` did not help.

This alternate version does not work either:

```FStar
let rec sum_versions (msg:message) : Tot nat =
  match msg with 
  | Literal version value -> version
  | Operator version [] -> version
  | Operator version (hd::tl) -> 
       (sum_versions hd) + sum_versions (Operator version tl)
```

This assertion fails:
```FStar
assert( Operator version tl << Operator version (hd::tl) );
```
So I don't know how to prove that the function terminates, without adding an height parameter to the type.

Why does the F* standard library include `min` but not `max`?

## Questions

I tried to create a lemma without `Lemma` by returning a squash type, but that seems only allowable in Ghost functions.
If we can't create a Ghost "All" function, how do we express proofs about other functions? Only as preconditions/postconditions
on the effectful function itself?  

