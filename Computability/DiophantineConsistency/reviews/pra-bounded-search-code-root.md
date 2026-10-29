# A finite PR bounded-search candidate

`PRABoundedSearchCode` constructs, for each fixed predicate code and
finite parameter tuple, a primitive-recursive candidate search code. In
every candidate-PRA equality model it proves the zero and recursive step
equations and expands the latter through the actual selector and predicate.
The intended least-counterexample, boundedness and universal-presentation
properties are not yet proved.

The independent replay `/tmp/pra-bounded-search-code-root-k5zdo5ki` passed
both modules without warnings, matched the author object hashes, and
reported only `propext`, `Classical.choice`, and `Quot.sound`. It used the
independently reviewed selector provider and checks current arithmetic
source/object hashes. Foundation, Mathlib, PRATheory and earlier code
objects remain inherited cache boundaries. The [evidence packet](pra-bounded-search-code-root-replay/)
preserves the author's first failed rewrite and final builds.
