## Day 4 solution notes

This one was entirely about parsing, but I didn't use a particularly structured
approach, other than using a `Map` to store partially-parsed entries.

### F* successes

Warned with an effect mismatch when I used `substring` instead of `sub`, then
correctly verified the latter without any additional work.

### Problems encountered with F*

Can the following lemma be proved?

```
let split_returns_list (x:string) :
  Lemma (ensures (Cons? (String.split [':'] x)))
        = admit()
```

The documentation is not clear that `FStar.IO.read_line` throws an `EOF` to
signal end of file, although that is pretty straightfoward (and obvious from
the ML source.)  But, the F* documentation doesn't mention exception-handling
at all so I just had to guess it worked the same way as OCaml.

I was a little surprised that I had to do 

```
try
  ... read_line ...
with
| EOF -> something
| _ -> something else
```

as it feels like EOF should be the only exception possible, but it didn't
validate without the catch-all clause.

I using `UInt64` because there's no parsing function for `int` (I think?)  But
this was painful because conversion from constant values to `UInt64.t` was
not automatic.

Syntax highlighting on GitHub doesn't recognize char literals, I think.
(The FStar tutorials don't mention them?)  This made matching `sprintf`
types unnecessarily eye-watering in the HTML doc.

### character ranges

Using `FStar.Char.char_code` seemed like it would more work than it's worth it.
Is there an easy way to represent the character range 0-9a-f?
