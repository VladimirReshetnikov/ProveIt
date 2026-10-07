# Formalization plan (not a checked Lean development)

1. Define additive k-cubes by their values at 0,e_1,...,e_k. Prove equivalence with the increment definition, the cardinality upper bound, and cube recursion.
2. Define additive energy, correlation, translation defect, and prove the energy-defect identity and subadditivity.
3. Formalize the 3/2 difference-set lemma, Markov extraction with threshold 1/12, and the 1/60 coset-rounding theorem.
4. Prove the exact energy-complement identity. Bound outside vertices by their number and establish the exact U2 profile.
5. Prove the boundary convexity inequality `(c+z)^k <= s^(k-1)*z + (2*s)^(k-1)*c` under `c+2*z <= 2*s`. Induct to the sharp boundary theorem, retaining the cancelling correlation sum.
6. Classify equality through support in one coset, maximal energy, and unions of two subgroup cosets.
7. Prove the exact U3 complement identity and discharge its positive terms. Establish the mixed polynomial comparison with a ring normalization plus elementary inequalities.
8. Prove the higher-dimensional two-coordinate Bonferroni bound and hole-cost comparison, then the exact higher-dimensional local profiles.
9. Formalize the finite Boolean-cube determinant census and odd-order refinement separately.
10. Only after compilation against the repository's actual Lean/mathlib versions should any file be described as formally verified.
