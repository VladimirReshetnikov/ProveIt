# Quoting standard PA194 source derivations in every IΣ₁ model

For the exact PA194 source language, this package supplies decidable equality
of the relation symbols and uses Foundation's existing translation from its
list LK derivations to `Derivation2`, followed by Foundation's typed quotation.
For any standard Foundation derivation `d`, any source theory `T` with the
stated `T.Δ₁` instance, and every arithmetic model satisfying IΣ₁,
`quoteDerivation` produces an internal `T`-derivation of the quoted conclusion
sequent.

`fixedStandardCode` strengthens this to one natural-number proof code, fixed
for the given standard derivation and theory, whose cast is the internal proof
code in every such model. It uses Foundation's model-uniform theorem
`Derivation2.coe_typedQuote_val_eq`.

The ordered source overlay check passed; the three printed theorems report
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`. The full nested
standalone script has not yet been replayed.

The input `d` is a **standard Lean derivation**. This is not a transformation
of arbitrary nonstandard proof codes and does not show a uniformly primitive-
recursive compiler, a PA194 machine simulation, or either direction of the
PA194/Con(PA) reduction in arithmetic. The definition produces an internal
Foundation proof; it is not an internal PA194 numerical-calculus proof.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-source-quote-models/check.sh`.
