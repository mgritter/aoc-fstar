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
  * ETA: it looks like `^*^` is an overloaded operator for this?
  
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

*ETA*: Fixed.  The missing piece is that there is no information that the
two varibles are not aliased!  Adding that as an extra assumption
succeeds.  The problem now is getting an environment set up where that is
true.  Because of the way I approached this function I "cheated" and the
references are global symbols, but that means the freshness proof is not
attached.  So I used an `assume`.

Compiling the full program is very, very slow and uses about 4GiB of memory.
Here's the profile:

`(Part2.fst(65,2-1069,9))	Query-stats (Part2.navigate, 1)	succeeded in 28445 milliseconds with fuel 2 and ifuel 1 and rlimit 163396800 statistics={mk-bool-var=259845 del-clause=233272 lazy-quant-instantiations=12377 interface-eqs=22 num-checks=6 conflicts=2119 binary-propagations=88860 arith-fixed-eqs=948 arith-bound-prop=5 propagations=365141 arith-assert-upper=1713 arith-assert-lower=1251 decisions=95919 datatype-occurs-check=22 rlimit-count=36479589 arith-offset-eqs=40 restarts=1 quant-instantiations=95468 mk-clause=251616 minimized-lits=1 memory=289.64 arith-pivots=1948 max-generation=16 arith-add-rows=5128 arith-conflicts=2 time=26.79 num-allocs=149681895193.00 datatype-accessor-ax=13 max-memory=331.81 final-checks=44 arith-eq-adapter=961 added-eqs=92863}
`

### Questions


