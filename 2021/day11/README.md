# Day 11 solution notes

I re-used my matrix code again, but this time put `ref`s inside it so that we didn't have to
re-walk the whole matrix in order to update flashing octopus neighbors.

## F* successes

I was able to make a small proof showing that an internal function successfully cleared the Flashed state.

`List.collect` continues to be a useful tool.

## F* problems

I really miss being able to write Lemmas. Is there anything we can do to prove properties of stateful functions
non-intrinsically?  Or does everything have to live in the pre- and post-conditions of the function?

I tried expanding my small proof to a bigger proof (that the whole row is cleared.)  This type-checks:
```FStar
let reset_octopus (m:octopi) (y:nat{y<=9}) (x:nat{x <= 9}) : All nat 
  (requires fun h0 -> forall (x0:nat) . x0 < x ==>  Normal? ( sel h0 (value_at m y x0)))
  (ensures fun h0 _ h1 -> 
       (modifies (only (value_at m y x)) h0 h1)
        /\ (forall x0 . x0 <= x ==> Normal? ( sel h1 (value_at m y x0))))
```
but all attempts to use it to reset a whole row have failed.

The error message that F* gives is not helpful at identifying what has failed.  Instead of identifying the precondition I get

```FStar
(Error 19) Subtyping check failed; expected type _: nat -> _: n: nat{n <= 9} -> FStar.All.ML nat; got type row_count: nat -> x: nat{x <= 9} -> FStar.All.All nat; Try with --query_stats to get more details
```

However, it does sometimes show the failing precondition as the 'related region'.

It might be that I need a non-aliasing precondition; even simple things variations fail in `reset_octopus_row`. But I'm not sure why?  Even if some of the values alias,
they should all inductively be reset.

## Questions

Is there a way to prove the correctness of our iterative procedure without declaring that (100C2) reference pairs are all unequal?
Presumably we could use something like
```FStar
forall x . forall y. forall x2 . forall y2. x2 <> y2 ==> (addr_of (value_at m y x)) <> (addr_of (value_At m y2 y2))
```
but that itself seems very hairy to prove.

Can we use preconditions with `fold_left` at all?  Unrolling the loop suggests it's not `fold_left` that's the problem here,
but I'm not sure.
