# Focused source audit and editorial actions

## Audited source

Repository: `VladimirReshetnikov/ProveIt`.
Commit: `9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`.
Canonical target: `Analysis/Polylogarithms/docs/manuscript/chapters/05-signed-kernels.tex`.
Git blob: `e61ff32263722d7575ca0202fba4dd7dad534861`.

The audit concerns the explicit colored depth-two matrix, its rank conjecture,
its Gaussian restriction and its S4 obstruction. It is not an exhaustive audit
of the entire consolidated manuscript.

## Promote the actual remaining conjecture

Promote `signed:conj:rank` and `signed:eq:rank-conjecture` to proved status.
Both individual odd-weight ranks are established uniformly in the article.
Retain the old labels as compatibility aliases, while changing the displayed
environment from conjecture to theorem. Add the even-weight extension and
complete nullspace description.

## Correct a logical overstatement

The source introduces the Gaussian-supported row-space dimension with
“Equivalently.” Projection and rank-nullity show that its dimension is the
**difference** of the two ranks. The pair of individual rank formulas implies
that difference, but specifying the difference alone does not determine the
individual ranks. Replace “Equivalently” by “In particular.” The new proof
establishes the two ranks separately and does not rely on the overstatement.

## Keep already correct material intact

The canonical weight-five matrix has 92 rows and 23 columns. Its old rational
separating witness is valid. The new integral witness is an alternative,
not a correction. The corrected stuffle color exchange is also valid and is
essential to the proof. Earlier Gaussian weight-six identities, one-two
reductions, signed-kernel theorems, and other integrated results are not
reclassified as new achievements of this continuation.

## Preserve unresolved status

Keep the S4 evaluation open. The stronger all-weight obstruction applies only
to rational linear combinations of the stated fixed-weight depth-two product
rows. It does not disprove an identity obtained from a larger relation system.
Do not infer numerical period independence from the formal kernel dimensions.

## Provenance policy

The historical arrival article and its experimental rank census are historical
evidence. Do not rewrite their assertions retroactively. Update the canonical
reading manuscript and its current editorial ledger, and add the new article,
code and receipts as a separate research contribution. The supplied helper
changes only the final canonical rank subsection and adds one fragment.
