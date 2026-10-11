# Proposed integration

Suggested report directory:

`Analysis/Polylogarithms/docs/reports/algebraic-gauss-centered-reflection/`

Preserve the ZIP's contents there as a report before changing canonical
claims. Keep this report's verification receipts distinct from any fresh
independent replay receipts. Nothing in this package was pushed or
committed to the live repository.

## Suggested canonical changes after independent audit

Place the algebraic residue proof and the full resonant-tail theorem
next to the existing Gauss successive-subtraction material. Update the
specific further-research question about a direct finite Bernoulli proof
as answered by this argument, while keeping its analytic predecessor
credited. The full tail formula is a separate extension, not just a
restatement of that question.

Place moving reflection, centered zeros, unique centering, and the Gamma
cumulant evaluation after the existing fixed-shift harmonic Laurent
calculus. Keep the notation crosswalk in Appendix A.3: our Z_r(s,a) is
E_r(s;a-1) in `twisted-harmonic-laurent`. In particular, our C_r(s) is NOT
a previously defined fixed-shift complete harmonic polynomial C_r(a).

`canonical_addendum.tex` contains a compact self-contained insertion for
the algebraic and moving-reflection results. It uses standard theorem,
proof, and corollary environments, and AMS math commands. Its one added
macro and all labels have an `agrcAdd` / `agrc-add:` prefix. The complete
article contains the extended proofs, Stieltjes normalization,
antiderivatives, and unequal-frequency result.

Add a version-specific bibliographic correction for the printed
Stieltjes-limit lower index in arXiv:2403.07123v1, not a blanket claim
about all editions of that source.

Do not mark S6, revised S8, higher spectral-derivative reduction, or all
incoming ZIPs as proved or audited on the basis of this delivery.

## Suggested acceptance gates

1. Review the integer-root/degree proof independently of its tests.
2. Verify the negative-power transform and both shift signs in the tail
   ODE, especially `1-exp(t)` rather than `1-exp(-t)` in its solution.
3. Check joint Mellin holomorphy at the protected divisors before
   extracting depth coefficients.
4. Replay `python code/verify.py --part all` on a fresh copy.
5. Rebuild and inspect the article PDF and the canonical insertion.
