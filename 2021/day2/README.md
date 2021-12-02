# Day 2 solution notes

This was very, very similar to the 2021 puzzle I solved with the ST effect,
so I decided to do it again but go bigger on the postconditions.  This
proved to be a problem.

I also misunderstood part 2 and proved the wrong things, and had to go
back and fix them.

### F* successes

Introducing deliberate bugs successfully caused type-checking to fail.
It was fairly easy to write the postconditions.

F* gave an error (tho not a helpful one) when heap variables weren't
initialized.

### F* problems

I was confused about if I should be using `sel_tot` or `sel`, but `sel`
works.

I tried to write a helper function that took two references and
created a set of their addresses, but that complained about mismatched
effects (GTot and St.)  I couldn't figure out a workaround, so
instead the code has lots of extra `addr_of`s.

This stupid function will not typecheck.  It's the < precondition that
fails.
  * The version in part 1 checks.
  * This version checks if I delete `depth := ...`
  * This version checks if I remove the inequality.
  * The asserts are fine, so the new value really is greater than the old value.
  * The tactics layer says the right logical condition is there!

WTF?!?!

```FStar
  let forward (d:int{d>0}) : ST unit
  (requires (fun h0 -> contains h0 horizontal /\ contains h0 aim))
  (ensures (fun h0 _ h1 ->
                        (sel h0 horizontal) < (sel h1 horizontal) /\
                        (modifies (two_element_set (addr_of horizontal) 
                                                   (addr_of depth)) h0 h1))) =
    let old_horiz = !horizontal in (                                                   
      depth := !depth + op_Multiply !aim d;
      assert( !horizontal = old_horiz );
      horizontal := !horizontal + d;
      assert( !horizontal > old_horiz )
    )
```

Tactics output:
```
Goal 1/1
d: d: int{d > 0}
p: st_post_h heap unit
h: heap
uu___: contains h horizontal /\ contains h aim /\
(forall (a: unit) (h1: _: heap{contains h horizontal /\ contains h aim}).
    sel h horizontal < sel h1 horizontal /\
    modifies (two_element_set (addr_of horizontal) (addr_of depth)) h h1 ==>
    p a h1)
a: unit
h1: _: heap{trivial_preorder int (sel h depth) (sel h depth + sel h aim * d)}
uu___'0: trivial_preorder int (sel h depth) (sel h depth + sel h aim * d) /\ contains h depth /\
modifies (Set.singleton (addr_of depth)) h h1 /\ equal_dom h h1 /\
sel h1 depth == sel h depth + sel h aim * d
a'0: unit
h1'0: _: heap{trivial_preorder int (sel h1 horizontal) (sel h1 horizontal + d)}
uu___'1: trivial_preorder int (sel h1 horizontal) (sel h1 horizontal + d) /\ contains h1 horizontal /\
modifies (Set.singleton (addr_of horizontal)) h1 h1'0 /\ equal_dom h1 h1'0 /\
sel h1'0 horizontal == sel h1 horizontal + d
```

Compiling the full program is very, very slow and uses about 4GiB of memory.

### Questions

How can we get this stupid trivial inequality to type-check?

