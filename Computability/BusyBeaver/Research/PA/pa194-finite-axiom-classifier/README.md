# Finite PA axiom-code classifier

In every arithmetic model satisfying IΣ₁, `peanoMinus_iff_sentence` identifies
membership in Foundation's actual internal Δ₁ classifier for `PeanoMinus`:
each accepted code is the numeral for one of its finitely many standard
sentences. The result applies to arbitrary, including nonstandard, input
codes. This ports the finite-list part of the PA196 upstream
`FoundationPAAxiomCodeComplete.lean` to the current Foundation.

This is a step toward the forward PA-to-PAeq axiom supplier: finite axioms
can be handled individually once their translated proof witnesses are
constructed. It does not supply those witnesses, address the induction schema,
or prove a machine/consistency implication.

From the repository root, with the matching audited Foundation overlay:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194-finite-axiom-classifier/check.sh
```

A direct Lean check against that overlay passed without `sorryAx`.
