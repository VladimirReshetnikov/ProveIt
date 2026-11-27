# Source and proof audit

## Upstream snapshot inspected

- Repository: https://github.com/lsernau/grh-lean
- Git tree/commit identifier returned for main on 2026-11-26: `72fead102f663d5c7a407964a13dc0cf9d977207` (the same abbreviated commit reported by the public reading note).
- Root README blob: `fdca72cbfa3557506543b662317267897e0058a0`.
- Compact README: `85d43d83a7fa3b496968ce9216f4a7d75e44e84a`.
- Compact GUIDE: `ca70306f0ee22fca325f7f515667e51625e8eabd`.
- Compact `src/Statements.lean`: `1cd1bce93344065936b2b392b23306254e0785ef`.
- Compact `src/Main.lean`: `a5d8389131c985a0b54ce5b0e778ee5c8126a997`.
- Compact `src/New/Main.lean`: `198ed5bf26aa294898931e0649bc2b88f1389f65`.
- Compact `src/Lib/Analytic/Landau/PolarLandau.lean`: `6b80c9062a74ecadcd9c51f9459cb3c71ac2ded9` (first 100 lines inspected).
- `Challenge.lean` has deliberately admitted statements for Comparator; according to the README it is not built or imported by the actual proof. This is not evidence of an admitted theorem in `src/Main.lean`.

The inspected code gives `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` as `New.grh`; the statement quantifies over all moduli and characters, excludes the principal pole, and requires Re(s)>1/2. `New.zeros_on_line` converts nonvanishing to the critical-line formulation. Upstream reports Lean v4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. The proof builds on a height/covolume comparison; this project does not claim to extend that comparison or independently audit every upstream module.

## New proof dependency map (human-readable)

1. Orthogonality at the identity class + Euler product => Mellin formula for `psi_q`.
2. Finite dilations => multiplier `P(b^s)` plus entire correction from integration below dilation cutoff.
3. Nonnegative zero multiplicities => no cancellation; sign at real zeros is positive after filtering.
4. Landau lemma (proved in the note using positive moments) => one-sided zero-free criterion.
5. PNT in fixed arithmetic progressions => `psi_q - theta_q = h_q sqrt(x)/phi(q) + o(sqrt(x))`; filter removes this term.
6. Classical truncated explicit formula and zero count => converse upper bound and exact exponent upper bound.
7. Under GRH, Abel limits of normalized prime errors equal filtered residues; positivity for every finite trigonometric polynomial => Hermitian matrix oscillation bound.
8. Irrationality of log(2)/log(3) => at least one of the bases 4,9 preserves any given nonreal critical zeta zero; establishes sharpness without numerical zero certification.

## Formalization path (not checked Lean code)

- Start with the five upstream public theorems and their Mathlib definitions; use the explicit `NeZero q` typeclass.
- Model `theta_q` and `psi_q` with `Finset.range (Nat.floor x + 1)` and indicators for primality / von Mangoldt and congruence; define real-coefficient filters as finite sums of dilation maps.
- Prove the Mellin identity first for Re(s)>1, including absolute convergence; use the log-derivative identity `LSeriesHasSum_mul_vonMangoldt` from `PolarLandau.lean` and character orthogonality. Prove the finite-interval term entire and determine residues via analytic order.
- Port the report's Landau lemma or adapt `IsPolar.landau` after scaling the error by x^{-1}; its source definition has extra hypotheses and a specific residue convention, so the import is not automatically a drop-in proof. Explicitly check all assumptions.
- Formalize the PNT in AP (fixed q), truncated explicit formula and zero counting estimates as required; availability in the pinned Mathlib must be checked. Do not silently assume them as axioms in a claimed verified result.
- Prove Abel limits for o(1) functions by splitting at a finite cutoff; build the Hermitian quadratic form directly before applying the finite-dimensional spectral theorem. Alternatively state the bound for every unit vector and avoid explicit eigenvalue machinery until the final step.
- For integer transfer use the elementary count of integers between consecutive dilated inputs. Finish the anti-aliasing argument using unique factorization of natural numbers.
- Audit all theorem dependencies with `#print axioms` and Comparator only after a real build. No Lean toolchain was available in the artifact environment; the new analytic results have not been kernel-checked.

## Literature search and status

Reviewed the user-supplied Wikipedia article, the compact repository documentation, Michael Rubinstein's verification page, DLMF §25.16, and search results on the truncated explicit formula and one-sided Chebyshev/RH criteria. Searches on dilation, prime products, and finite differences did not establish an exact antecedent of the combined theorem. Classical one-sided criteria, spectral methods, and prime races are related prior work. Priority remains unverified. The proof's only use of GRH is explicitly marked; the equivalence and exact exponent as a function of the zero supremum are unconditional statements.
