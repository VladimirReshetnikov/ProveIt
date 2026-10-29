# Candidate PRA bounded-search invariants and semantic induction bridge

For any fixed predicate code and finite parameters, `PRABoundedSearchInvariant`
and `PRABoundedSearchMinimal` prove in arbitrary candidate-PRA equality
models, and as two closed candidate-PRA sentences, that the found index is
either bad or the bound, and that it is zero or its predecessor is good.
`PRABoundedSearchUniversalRule.inductionFromSearch` then proves, on any
carrier, that these two conditions together with bitness, successor
exhaustion and the base/step conditions imply Boolean induction. This is a
semantic bridge; no universal theory or equivalence of presentations is
claimed yet.

The independent replay `/tmp/pra-search-invariants-root-jw3cbacu` passed
all six modules without warnings and matched the author object hashes;
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
It uses the reviewed search-code provider and checks current arithmetic
source/object hashes. Foundation, Mathlib, PRATheory and earlier code
objects remain inherited cache boundaries. The [evidence packet](pra-search-invariants-root-replay/)
preserves the author's exploratory attempts, including failed elaboration.
