# From a positive-domain all-model bridge to an iPRA derivation

For any finite expression `e : Expr (Fin n)`, `PositiveModelBridge e` is the
explicit assertion that **in every** model of `IΣ₁`, a strictly positive
internal zero of `e` exists if and only if the internal 215-state machine
halts. `bridge_of_positive` converts this two-way hypothesis into the existing
`HAExpressionAssembly.PolynomialBridge (positiveShift e)`: an unrestricted
model zero of the exact once-shifted syntax corresponds to a positive zero
of the original syntax. The reverse coordinate map is `v ↦ v−1` and is
used only after the positive-coordinate hypotheses.

`native_equivalence_of_positive` then invokes the existing
`IPRAExpressionNative.equivalence_of_bridge` and proves in Lean that the
repository's native iPRA theory derives the equivalence between the literal
no-zero sentence for `positiveShift e` and its selected Foundation ZFC
consistency sentence. This is a conditional proof-producing theorem: it does
not assert `PositiveModelBridge` for the compact graph, identify the fixed
integer ports or displayed PDF, or discharge either model direction.

The inherited proof chain is specialized. It uses first-order completeness
for the **exact** all-model no-zero statement, then a checked bounded-ZFC-
refutation/strict comparison and the repository's intuitionistic translation.
It does not claim a general unrestricted transfer of arbitrary `IΣ₁` theorems
to iPRA. The target is the repository's specific `nativeTheory` and
`mappedNativeRefutation embedding`; the interpretation and adequacy of those
objects retain their own documented source and replay conditions.

The bounded author attempt 03 exited 0 in 6.396 seconds with no warnings or
`sorryAx`. Source SHA-256 was
`4faabe0a42f1adabe102e58c4355ddbdf03f9c0ccb29498c48c99241066356ea`;
object `/tmp/positive-model-ipra-adapter-author-gzcg51tr/PositiveModelIPRAAdapter.olean`
had SHA-256
`8955395f621d3b4445bbe56ad3660be21b4f2d3b15f15cb384340a163cd81c12`.
The direct dependency companions and all 1,497 live selected provider files
were unchanged. This is a single-author check over inherited nine-variable
provider ancestry, not a fresh paired replay or package-transitive/dynamic
closure audit. Lean reports `propext`, `Classical.choice`, and `Quot.sound` as
metatheoretic dependencies; they are not stated as iPRA axioms.

Attempt 01 used an older provider without explicit model-bridge imports;
attempt 02 used the guarded nine-variable provider and failed on a missing
lemma name in the positivity subgoal. Their sources and logs are preserved;
attempt 03 supplies the positivity proof directly.
