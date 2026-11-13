# Signed first-root branches of the speculative graph

`Absorb89Signs.first_branches` proves in every IΣ₁ model that an actual speculative-graph output zero, positive beta and positive witnesses yield a positive first root, positive `Bt=q*(Bp-Bn)`, its first Pell equation, and one of the exact positive or negative signed-root equations printed in the Lean source. It uses the checked first-factor transport `Bn<Bp`, so the natural subtraction defining `Bt` is justified. This is a graph-specific sign disjunction, not a reverse graph witness map.

The graph-specific [divisibility theorem](DIVISIBILITY.md) has since supplied
the required first transport divisibility in either branch. The
[negative-branch reflection](REFLECTION.md) constructs a witness above `s`
and proves its first-root equation; a separate model theorem preserves the
full graph zero. The [positive branch](POSITIVE_BRANCH.md) has since acquired
its growth condition under the fixed-port bounds. The count of 89
live operations has been checked externally against the Lean graph. A later
[join](EQUIVALENCE.md) proves reverse existence under the fixed-port bounds;
a further [halt bridge](HALT.md) and [iPRA join](../ordinary12-absorb89-ipra-join/README.md)
have since passed author checks with the stated provider limitations.

Attempt 01 failed on proof normalization and is retained. Attempt 02 passed with no reported warnings. Source SHA-256 is `fc86d9adce047925fcb2be9d4f7bf94ce6a3cc648dcbe93ffbf11a79b804cfc2` and output object is `f35548f300885a25a36dbe1aaf5977f111105da4a2720186d4755cfbbe561437`; both axiom reports list `propext`, `Classical.choice`, and `Quot.sound`. The transport and predecessor objects and selected 1,291-object union were pinned and rechecked. Imported first-norm source locally suppresses unused-variable and unused-simp-argument linters. Package, dynamic, and source-to-object ancestry remain inherited rather than freshly rebuilt; exact resource samples and hashes are in the receipt.
