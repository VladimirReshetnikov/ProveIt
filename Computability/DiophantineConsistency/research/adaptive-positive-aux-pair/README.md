# Signed auxiliary expression in a constructed run witness

`ArithmeticAdaptivePositiveAuxPair2011` binds the strict auxiliary seed
orientation to the exact signed expression `eV` at the fixed ports. Its run
theorem states that any internal halting time yields a positive thirteen-input
adaptive zero whose signed auxiliary pair has negative side strictly less than
positive side. The radix inequality needed for this binding is derived from
that positive zero and its transport equation.

This establishes a sign for a specifically constructed witness; it does not
assert the sign for all zeros. Passing the witness and sign through the named
graph extensions is a separate obligation. The [paired replay](../../reviews/adaptive-positive-aux-pair-replay/README.md)
reuses the oriented-seed provider and inherits its transitive ancestry.
