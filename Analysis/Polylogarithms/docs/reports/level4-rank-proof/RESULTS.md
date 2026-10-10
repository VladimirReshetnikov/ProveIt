# Result and evidence ledger

## Proved uniformly in the article

1. **All-weight ranks (Theorem 1.1).** Both odd-weight formulas in the
   manuscript's `signed:conj:rank` are proved. The even-weight matrix has full
   column rank, as does its deleted-column submatrix.
2. **Complete nullspace (Theorem 4.1).** At odd weight w=2m+1, the kernel is
   the direct sum of two m-dimensional polynomial reflection blocks. The
   displayed vectors are an integral basis over Q. No claim of saturation as
   an integral lattice is made.
3. **Gaussian saturation (Corollary 5.1).** The Gaussian-supported part of the
   specified row space is exactly the same-point shuffle span in odd weight.
4. **Membership certificates (Corollary 5.2).** Testing tK_w=0 is necessary
   and sufficient. A nonzero pairing supplies an explicit separating vector.
   Basis construction and membership use O(w^2) integer arithmetic operations;
   the article states a conservative bit-complexity bound.
5. **Uniform harmonic-sum obstruction (Theorem 6.1).** S_(2m) adds one formal
   direction to the Gaussian span in the quotient by this fixed linear row
   system. This is not a statement of numerical independence.
6. **Even-weight compiler (Theorem 7.1).** Explicit substitutions recover all
   retained imaginary double coordinates from singles and products of singles.
   This is a constructive specialization of the known parity phenomenon.
7. **Odd-weight coordinates (Corollary 7.2).** Affine centering leaves m
   Gaussian and m complementary polynomial coordinates in this system.
8. **Two mixed leading-index families (Theorem 8.1).** For m>=1, the article
   proves all-weight formulas for Im Li_(2m-1,1)(i,i) and
   Im Li_(2m-1,1)(i,-i), plus their difference.

## Exact computational support

- All 40 weights from 2 through 41: integer kernel annihilation, independent
  kernel columns, modular rank lower bounds and matching rational upper bounds.
- The deleted-Gaussian-column ranks are independently certified in all 40 weights.
- 210 even-weight formulas through weight 12 satisfy all 816 retained rows.
- 420 Gaussian shuffle membership checks.
- Six odd-weight affine compatibility checks (weights 3 through 13).
- Twenty uniform S_(2m) witnesses (odd weights 3 through 41).
- Sixteen leading-family comparisons (two per even weight 2 through 16).
- At weight five, the complete 92-by-23 matrix is supplied. Rational ranks are
  also recomputed directly. The new integer witness has target pairing 7.

## Diagnostic, not rigorous interval evidence

Fifty-four independent nested-series comparisons, with 4096 outer terms and
70 decimal working digits, lie within the analytic absolute-tail bounds.
The largest observed discrepancy/bound ratio is approximately 0.797.
Floating-point rounding is not enclosed, so these are diagnostics only.

## Not resolved or claimed

- The manuscript's proposed S4 numerical evaluation.
- Numerical period independence or minimal analytic depth.
- Completeness of all standard cyclotomic relations.
- An integral-lattice basis or Smith normal form.
- A new general parity theorem or exhaustive worldwide novelty certification.
- Lean verification, independent peer review, or a rebuild of all 228 source pages.
