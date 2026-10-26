# Direct quartic companions

These are direct numerical-C222 proof-calculus equations. They contain no
machine coefficient tuple, K215 simulation, Jones reduction or variable
exponent. Each final equation is the sum of the squares of its explicit
quadratic residuals, with exact expanded coefficients supplied separately.

| Directory | Domain | Variables | Rows | Monomials | Height |
|---|---|---:|---:|---:|---:|
| radical233 | integers | 233 | 169 | 10,379 | 12,874 |
| radical234_sparse | integers | 234 | 170 | 4,858 | 13,448 |
| natural204 | naturals including zero | 204 | 156 | 8,213 | 130,686,374 |
| natural203 | naturals including zero | 203 | 155 | 8,237 | 799,349,232 |
| natural203_sparse | naturals including zero | 203 | 155 | 8,263 | 207,116,893 |
| natural203_reduced | naturals including zero | 203 | 155 | 49,682 | 481,920 |

All are degree four. Domain and coefficients are part of the equation.
The final two are optional row-basis tradeoffs on the same natural coordinates.
The 233-integer result is a direct composition of package159's common-Hessian
projection with package164's integer source. The natural reductions require
the separate new domain argument in NATURAL_PROOF.md. The first two natural
projections have canonical CRT completeness, while the third has a pointwise
natural inverse certified by a retained nonnegative-square row.

The inherited theorem and these proofs establish within ZFC that each
equation's unsolvability in its stated domain is equivalent to Con(ZFC).
This is an ordinary mathematical proof, not a new end-to-end Lean/Rocq
formalization, a proof of consistency, or a global simplicity minimum.

## Check and reconstruct

Only Python's standard library is required.

    python3 -B verify_direct.py --receipt /tmp/direct-check.json
    python3 -B -O verify_direct.py --receipt /tmp/direct-check-optimized.json

The checker is independent of the constructors. It checks the exact
directional derivative, constant slopes, every quadratic restoration and
projected coefficient, natural restoration obligations, complete SOS
expansions, row-basis inverses, and deliberate corrupted-certificate controls.
It does not search for a solution or prove the inherited arithmetic calibration.

In a disposable copy, the main natural equations can be rebuilt with:

    python3 -B build_natural.py

The integer targets can be reconstructed in a fresh directory using:

    python3 -B reduce_radical.py integer_source239.json /tmp/rebuilt233
    python3 -B reduce_radical.py integer_source240_sparse.json /tmp/rebuilt234

The optional row reductions are independently reversible and need not be
rediscovered to check them. `reduce_basis.py` supplies the discovery algorithm.

## Source boundary

All repository inputs are pinned to
`fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`.
The three immediate parent residual lists are included as source JSON files,
with the original package164 natural and integer proofs beside them. These
proofs name their earlier arithmetic and C222/ZF/ZFC dependencies. The exact
new algebraic reductions are independently replayable from the bundled source
lists; this component does not claim a fresh replay of every earlier release.

Source URLs and file digests are in SOURCE_LEDGER.json. The projection
constructor, row-reduction code and independent projection checker derive
from package159, with the checker extended to separate algebraic identities
from natural-domain obligations. The canonical sign choices derive from164.
New source and proofs are AI-assisted research under the inherited MIT No
Attribution license, retained in LICENSE.

The separate split-seed experiment was investigated and then excluded from
this deliverable: package156 had already considered that calculus split,
and its new measured form did not improve the chosen natural equation.
