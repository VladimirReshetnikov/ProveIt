# Sources, provenance, and contribution boundary

Research date: 4 October 2026.

## Pinned ProveIt source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Revision inspected:
`79e7aab60ee856862b36c38cf32cfdb1be95313f`

Main file:
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions/article.tex`

Main-file blob:
`73a53d9784260c2f0d083f2baa62a5535f6d6105`

Pinned URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/79e7aab60ee856862b36c38cf32cfdb1be95313f/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions/article.tex

The associated README was also inspected. Its blob was
`59ad8b15b9522102e1f6d48f68c1db358a3ac044`.

The consolidated report has Parts I and II dated 1 October 2026 and Part III
added 3 October 2026. The repository describes it as AI-assisted, unrefereed,
and not formalized. Its stated prior results are used as mathematical results,
not as independently certified facts from a proof assistant.

### Prior results explicitly credited

- The all-orders combinatorial expansion of e*a(n)/n! and its rigorous fixed-order
  remainder, by stable path-forest moments and inclusion–exclusion.
- Rational collapse and all-orders integrality for directed offsets.
- The auxiliary formal series Psi, its differential equation and recurrence.
- The shifted Stirling transform of its coefficients.
- The entire identity B(t)=E'(exp(t)-1), proved in Part III, Section 30,
  label `spf:rc:thm:Borel`.
- Lambert-W/Gamma-scale index inversion, including the first displayed algebraic
  corrections in the present report.

The pinned source explicitly says its entire-transform theorem does NOT prove
Borel–Laplace summability or convergence of the inverse-power series. It leaves
large-order growth, a justified truncation rule, and beyond-all-orders
corrections unresolved. The specific caveat was fetched again at the pinned
revision to confirm that it had not been silently superseded.

### Extensions developed in the present manuscript

- Explicit Dawson–Volterra representation for the A189281 Borel kernel.
- Exact positive-axis asymptotics, including both integration constants.
- Positive-ray summation and meromorphic continuation of a specified completion.
- Sharp horizontal-strip threshold and failure of angular-sector exponential bounds.
- Sharp double-exponential maximum growth and the logarithmic coefficient-root law.
- Non-P-recursiveness of the correction coefficients, not of the integer counts.
- A proved growing-order truncation rule for the analytic completion.
- Exact inhomogeneous shift equation, a fourth-order homogeneous equation, and
  analytic realization of the displayed order-13 OEIS operator.
- Arithmetic proof of a nonzero flat discrepancy in every block of four indices.
- Propagation of that flat discrepancy to the smooth inverse.

All purely analytic results can be formulated directly from the explicit formal
Psi, independently of the prior combinatorial proof. The statement that the
counting discrepancy is flat uses the prior all-orders counting theorem.

## Public primary sources consulted

1. OEIS A189281, https://oeis.org/A189281
   Definition, first 22 values, displayed correction coefficients, conjectured
   recurrences, and Mark van Hoeij's T–U–V factorization. The entry was still
   labeling the counting recurrence conjectural when consulted. Numerical
   values are validation targets, not inputs to the coefficient proofs.

2. George Spahn and Doron Zeilberger, *Counting Permutations Where The Difference
   Between Entries Located r Places Apart Can never be s (For any given positive
   integers r and s)*, arXiv:2211.02550 (2022).
   https://arxiv.org/abs/2211.02550
   Source context for the exact matching-of-tilings method; that elementary
   formula is reproved in Appendix A rather than claimed as new.

3. Manuel Kauers and Christoph Koutschan, *Guessing with Little Data*,
   arXiv:2202.07966 (2022).
   https://arxiv.org/abs/2202.07966
   Context for guessed recurrences, not a theorem assumed in the analytic proofs.

4. NIST DLMF 7.2, https://dlmf.nist.gov/7.2
   Dawson and error-function definitions.

5. NIST DLMF 7.12, https://dlmf.nist.gov/7.12
   Error-function asymptotic expansions, sectors, and remainder conditions.

6. NIST DLMF 6.6, https://dlmf.nist.gov/6.6
   Small-argument expansion of the exponential integral E1.

7. NIST DLMF 2.3, https://dlmf.nist.gov/2.3
   Watson's lemma; the precise local/tail argument needed here is given in the text.

8. NIST DLMF 2.11, https://dlmf.nist.gov/2.11
   General context on remainder terms and Stokes phenomena.

9. NIST DLMF 5.11, https://dlmf.nist.gov/5.11
   Gamma/Stirling asymptotics and inverse-index estimates.

## Priority and status

The definite novelty comparison is with the pinned ProveIt report. The source
search was targeted, not a comprehensive historical literature review. No claim
that these results have never appeared elsewhere is made. The absence of a
proof on an OEIS page is not evidence that no published proof exists.

The full original counting recurrence is not proved here. An analytic completion
can satisfy that operator and still differ from the integer counts, as this
manuscript proves. The positive-ray completion is not asserted to be a complete
resurgent transseries, nor is its truncation error automatically the counting
error. All numerical diagnostics are explicitly non-interval-certified.

No original repository files, third-party source code, font files, or copied
papers are included. The mathematical data excerpt is credited to OEIS; all
new programs in this archive were written for this report. No external account,
repository, or OEIS entry was modified.
