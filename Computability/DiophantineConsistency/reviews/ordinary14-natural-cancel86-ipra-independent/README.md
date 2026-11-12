# Independent source review: natural-86 proposed iPRA adapter

The proposed `SameNoZero` proof uses the pointwise natural86/shifted-74 zero
iff in the correct opposite directions under negation, at the same valuation
and `CompactSymbolicModelIff.p` tuple. The `HAExpressionNoZeroEquiv.bridge`
arguments have the correct orientation: the natural86 expression is the
conclusion and the existing root74 positive bridge supplies the once-shifted
comparison bridge. The final no-zero sentence is applied to natural86 directly;
no second positive shift is introduced.

The native declaration uses `equivalence_of_bridge`; the standard declaration
uses the existing standard/native provability iff in the right direction; the
reference declaration applies equality-only erasure to that native derivation.
The statements propose derivability of biconditionals, not a proof of either
side. The checker replays the separately reviewed ring/model source receipt,
pins the earlier root74 bridge review, checks interfaces and symbolic tuple,
and runs a small negation-direction control.

This is source review only. All imported drafts and tactics remain
unelaborated. Provider and axiom closure, any proved iPRA endpoint, formal
circuit-size correspondence, symbolic-port-to-byte identity and PDF binding
remain open. No Lean was run.
