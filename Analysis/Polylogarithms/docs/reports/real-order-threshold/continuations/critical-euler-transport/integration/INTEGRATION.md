# Integration map

Keep this delivery whole at:

    Analysis/Polylogarithms/docs/reports/critical-euler-transport/

The predecessor is `docs/incoming/ProveIt_RealOrder_Threshold.zip`. Its delivered
source labels the sharp-constant conjecture `conj:constant` (Conjecture 12.3).
Promote that claim to a theorem and cite this article's Theorem 3.2. Do not
silently rewrite the historic delivered article; record the status change in the
programme ledger and use an editorial cross-reference.

The new signed-kernel material can be summarized by the accompanying
`05-critical-euler-transport.tex`, whose labels start `criticaleuler:`. The
fragment is meant for an existing `article`/`book` preamble supporting amsmath,
amsthm, and the theorem environments. It does not add macros or bibliography
keys that could collide. It refers readers to the full proof article by title.
No automatic source-tree patch is included, because the incoming predecessor
may be integrated at a different path before this package is incorporated.

## Preserve the distinctions

1. The critical signed measure contains its atom. Its ordinary Gaussian series
   does not converge; the analytic/Abel value is used.
2. The all-depth sharp constant decreases in outer order, but individual scaled
   finite-depth errors do not. Preserve the exact R_128 reversal.
3. Use the endpoint-uniform estimate for optimizing over parameters, not the
   compact-uniform fixed-order expansion.
4. The rate-one beta–gamma transport has an extra numerator X. It is not the
   earlier rate-two normalization with that factor removed.
5. The limiting density at a=0 has infinite total mass; its Euler-filtered
   integrals are nevertheless finite.
6. Do not promote numerical local maxima or the eventual-unimodality conjecture
   to theorems. The drift theorem deliberately covers every maximizer without
   asserting uniqueness.

The prior S4 proofs remain prior material. S6 and the remaining angular/radial
conjectures are not resolved by this package. No upstream write was performed.
