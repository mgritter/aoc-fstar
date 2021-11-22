# Day 18 solution notes

This day was _also_ all about parsing, and it took me a long time to find
an approach for writing a parser-combinator library that would work.
(Recursive descent was overkill, simple stack-based parsing would have been
better.)

However, the approach I took was to parse into an AST.  The problem is that
AST was left-associative (due to use of recursive-descent parsing) and so
it was unsuitable for *both* parts of the problem, and had to be transformed.
Fortunately the transformation was not too hard to write.

Other than proving the parser succeeds, I was not able to get a lot of
value out of dependent typing on my first pass.  I don't know if with a
simpler parser I would have been able to encode the precedence rules as a
type.

The parser is a mess because in order to define it recursively, we need to
prove that each invocation of `parse_ast` operates on a shorter string
(or some other well-founded partial order.) This means some combinators need
to take the original input string (as a "context" argument) and only
call parsers with inputs that are less long than that. But I discovered this
very late in the process so the library doesn't have a coherent way of
organizing this information.  (A subsequent attempt failed because it doesn't
seem like it can be inferred, which would be helpful.)

### F* successes

In part 2, I accidentally wrote

```FStar
rewrite_mul = ...
    | Add a t -> rewrite_mul left_op (rewrite_add (rewrite_prec a) t)
```

instead of

```FStar
rewrite_mul = ...
    | Add a t -> (Mul left_op (rewrite_add (rewrite_prec a) t))
```

F* alerted me that this would not terminate.

F* really requires you to prove that your recursive-descent parser will
terminate.  This is a mixed blessing.

### Problems encounted with F*

I spent much happy time proving things about substrings.  The F* standard
library doesn't have any axioms about `sub` so I introduced this one:

```FStar
// Sublist of a list starting at i and taking j elements
let rec sublist #a (i:nat) (n:nat) (l:(list a){length l >= i+n}) : (x:(list a){length x = n}) =
  if n = 0 then []
  else if i > 0 then match l with
  | hd :: tl -> (sublist (i-1) n tl)
  else match l with
  | hd :: tl -> hd :: (sublist 0 (n-1) tl)

let substring_is_sublist (s:string) (i:nat) (l:nat{i+l <= strlen s}) : 
  Lemma (ensures (sub s i l) =
                 (string_of_list (sublist i l (list_of_string s))))
     = admit()
```

I was a little surprised that string literals do not automatically match
an implicit type of the form `s:string{strlen s>0}` but you can
prove this about individual literals with a normalized assertion, something
like:

```FStar
let foo_tok = assert_norm( strlen "foo" = 3); "foo"
```

I switched to character tokens anyway.

The F* tutorial did not mention that you could put a `<` or `<<`
refinement type on an argument to help the termination proof along.
This is (I think?) the only way to create mutually-recursive functions
that accept each other as arguments.  See [ExampleInduction.fst](../../doc/ExampleInduction.fst).

Figuring out how to get the OCaml modules to find each other was needlessly
frustrating, it's just a matter of `I ./out'.

OCaml complains a *lot* about missing cases in the extracted matches.

I am very puzzled by this F* behavior, which I cannot reproduce in a smaller
example:

```FStar
type digit_string = (x:string{x = "0" \/ x = "1" \/ x = "2" \/ x = "3" \/ x = "4" \/ x = "5" \/ x = "6" \/ x = "7" \/ x = "8" \/ x = "9"})

// This definition fails if one of the possibilities is missing!
// ... or out of order.  Exciting!
let digit : (parser digit_string) =
    parse_rename "digit" (literal_char '0' <|> literal_char '1' <|> literal_char '2' <|> literal_char '3' <|> literal_char '4' <|> literal_char '5' <|> literal_char '6' <|> literal_char '7' <|> literal_char '9' <|> literal_char '8')
```

```
(Error 19) Subtyping check failed; expected type parser digit_string; got type input: string
  -> Prims.Tot
    (parse_result (z:
          string
            { z = string_of_list ['0'] \/ z = string_of_list ['1'] \/ z = string_of_list ['2'] \/
              z = string_of_list ['3'] \/ z = string_of_list ['4'] \/ z = string_of_list ['5'] \/
              z = string_of_list ['6'] \/ z = string_of_list ['7'] \/ z = string_of_list ['9'] \/
              z = string_of_list ['8'] })
        input); The SMT solver could not prove the query, try to spell your proof in more detail or increase fuel/ifuel
```

Everything works OK (-ish) if the parsers are in the right order, but the
proof fails if they are out of order.

A problem you'll notice; the Github F* syntax formatter doesn't like char
literals.  I *think* it's the grammar from this library? https://github.com/FStarLang/atom-fstar  That is the one mentioned here: https://github.com/github/linguist/tree/master/vendor
