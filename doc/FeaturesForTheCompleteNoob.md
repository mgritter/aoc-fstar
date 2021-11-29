# Features of F*

Not all features of the F* language are mentioned in the tutorials. Some are
in wiki pages, and some just seem to be folk knowledge.  This page attempts
to capture a list.

## Dependent pairs and tuples

> the correct syntax for defining a dependent pair type is (x:a & b(x)) (if the parens are necessary)
-- https://github.com/FStarLang/FStar/wiki/Moving-to-menhir and https://github.com/FStarLang/FStar/wiki/Recent-backward-incompatible-changes

> `&` is overloaded for both dependent and non-dependent tuple types.
-- https://github.com/FStarLang/FStar/wiki/F%2A-symbols-reference

## Parameters that start with $

> The stratified specific = qualifier is not available anymore on binders i.e. the deprecated fun (=x:t) -> ... must be changed to fun ($x:t) -> ...
-- https://github.com/FStarLang/FStar/wiki/Moving-to-menhir and https://github.com/FStarLang/FStar/wiki/Recent-backward-incompatible-changes

> equality constraint for unifier; in `val f : $x:int -> y:int -> int`, F* will allow any `y` that is a subtype of `int`, but `x` must be exactly of type `int`.
-- https://github.com/FStarLang/FStar/wiki/F%2A-symbols-reference

## Manipulating connectives in classical logic

You can perform operations on existential or univeral qualifiers without messing with FStar.Classical and FStar.Squash:

https://github.com/FStarLang/FStar/wiki/Sugar-for-manipulating-connectives-in-classical-logic

## Arrow types with caret?

What does `^->` mean?

Used in `FStar.map` but not defined in  https://github.com/FStarLang/FStar/wiki/F%2A-symbols-reference

## Type ascription

The `<:` operator requires that its left argument be of the type on the right.
