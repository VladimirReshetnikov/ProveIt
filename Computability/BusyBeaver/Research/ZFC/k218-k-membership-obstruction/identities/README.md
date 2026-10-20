# Adding every identity still does not calibrate K + RAB

The [ordinary syntactic proof](proof.md) shows consistency of K plus
`rho8(A,B,C,R(A,B))` even after adding **every identity** `X → X`. The exact
retained rho1–6, merged G, full gated C222 bundle, truth, MP and theorem-only
GEN remain present. Thus the cheaper proposed extra fixed axiom
`F → F`, numerical code 16, is covered too.

The proof constructs a grammar of safe codes and eliminates modus ponens by
induction on the sum of two certificate sizes. Two added grammar constructors
record weakening and the known transport rule from a closed theorem. The
literal `req`/`nks` structure prevents weakening from activating the bundle;
replacing that structure by an arbitrary quantified core would be invalid.
The grammar excludes falsum by its constructor tag. All native-code cases,
including `I(0,0)=0`, are included.

An [independent mathematical review](peer.json) checked every forbidden minor,
the rho8 trigger, and the swapped-premise size descent and found no defect.
The exact reviewed proof bytes are preserved, including its original draft
heading. The elementary certificate argument is formalizable in PA; no new
Lean or Rocq execution is claimed. Assuming Con(ZFC), it rules out the desired
ZFC-provable calibration of this strengthened calculus. There is no machine
construction or source-pricing claim.

This settles the extension considered by the earlier
[fixed-code16 diagnostic](../fixed-code16/README.md), **without QS**. It does
not include quantified double-negation elimination: that axiom invalidates
this grammar's quantifier-stripping lemma. In particular, the separate
[three-value proof](../proof.md) for K + RAB + QS and this consistency proof
for K + RAB + all identities must not be combined to claim consistency of
their union. K + RAB + fixed16 + QS remains open here.

`opening_encoder` authored the new grammar and ordinary proof;
`review_upstream_reflection` independently reviewed it. The construction
extends the earlier [RAB invariant](../../k219-fourth-parameter/diagonal-invariant/DiagonalInvariant.lean)
while replacing its arbitrary-core bundle approximation with the literal
seed bundle. [Source bindings](source-freeze.json) and
[publication provenance](publication.json) preserve that lineage. No checker
execution is needed to reproduce this ordinary source review.
