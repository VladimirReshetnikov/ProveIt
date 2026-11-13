# Reverse factor bridge for the free-J literal

`FreeJCompletenessFactorBridge.zero_of_factor_units` proves, in any model of
`IΣ₁`, that when each of the actual free-J literal's three signed factors
represents positive one at a valuation, the actual literal is internally zero
at that valuation. It works for arbitrary integer coefficient ports and does
not assume positive coordinates. `zero_iff_factor_units` joins this new reverse
implication with the existing `literal_factor_units` theorem, giving an exact
if-and-only-if for the same 95-operation free-J expression. Its forward
implication uses the existing modulo-four exclusions.

This is a conditional composition lemma: it does not construct a positive
valuation or establish the three factor equations from a machine halt, bind the
retained coefficient ports to the displayed equation, or construct a proof in
iPRA. In particular, the 100-operation graph in the neighboring ordinary-unit
products note has a different `J` parameterization; its informal completeness
argument is guidance, not a Lean proof of this free-J graph.

The bounded single-author `attempt03` exited 0 in 2.685 seconds, with no warning
or `sorryAx`. Source SHA-256 was
`ecb2c61425fb0307caf925d55d743096938373cba4c368f426d8ff5071d10131`;
object `/tmp/free-j-completeness-factor-author-q9rapr3k/FreeJCompletenessFactorBridge.olean`
had SHA-256
`f516093a340fe3c6cf8b5998ee791b734a9e9dec7a7fd7d7ad5e350aa25fade4`.
The direct dependency/companion guards and all 97 live files in the selected
free-J power author overlay were unchanged. This does not re-audit historical
provider ancestry, package-transitive dependencies, or constitute an independent
replay. `#print axioms` reports `propext`, `Classical.choice`, and `Quot.sound`
for both theorems; these are metatheoretic Lean dependencies, not axioms claimed
as part of iPRA.

Attempt 01 failed because the historical free-J provider contained a dangling
transitive object symlink; no proof was checked. Attempt 02 used the surviving
author overlay but failed because the `pairEval` namespace was not open. Both
failed sources and logs are preserved under `observations/`; attempt 03 added
the namespace, without weakening the theorem statement. The runner rejects
errors, warnings, `sorryAx`, changes to the source or guarded files, and a
missing object.
