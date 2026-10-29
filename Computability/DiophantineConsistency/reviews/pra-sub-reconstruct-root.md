# Candidate PRA subtraction reconstruction

`PRASubReconstruct` derives the closed candidate-PRA sentence
`y-x=0 ∨ x+(y-x)=y` for all x and y. Its parameterized open induction
argument works in every equality model and uses predecessor exhaustion;
first-order completeness yields the actual candidate-theory derivation.
This supplies the reconstruction ingredient for the hard direction of the
Q order clause, but does not itself complete that clause.

The independent replay `/tmp/pra-sub-reconstruct-root-_au_csn3` passed both
files without warnings, matched the author object hashes, and reported
only `propext`, `Classical.choice`, and `Quot.sound`. It used the reviewed
subtraction-laws provider and the current-source refreshed subtraction
object. Foundation, Mathlib, PRATheory and earlier prerequisite objects
remain inherited cache boundaries. Author attempts, including an early
rewrite failure, are preserved in the [evidence](pra-sub-reconstruct-root-replay/).
