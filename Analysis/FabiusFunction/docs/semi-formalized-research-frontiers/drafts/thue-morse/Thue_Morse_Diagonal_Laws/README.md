# Thue–Morse Diagonal Laws

*Diagonal Polynomials and Dyadic Block Geometry in Repeated Thue–Morse
Summation* — a consolidated volume (64 pp A4, 3,700 source lines, 15
chapters, 4 appendices) assembled on 2026-09-05 from the three
diagonal-polynomial reports that arrived together on 2026-09-03:

- `thue_morse_diagonal_polynomials/` — *Diagonal Polynomials and Dyadic
  Block Geometry in Repeated Thue–Morse Summation* (24 pp). The spine of
  the volume: its chapter order, notation, and the statements and proofs of
  every result all three reports shared.
- `thue_morse_diagonal_polynomials-2/` — *Diagonal Polynomial Laws in Odd
  Iterated Thue–Morse Summation: Riordan-array structure, 2-adic Bell
  recurrences, exact arithmetic, and fast Wolfram Language evaluation*
  (37 pp). Contributed the Riordan-array chapter, the arithmetic chapter
  (primitive normalization, exact denominators, rational-root
  restriction), the partition/determinant and translation formulas, the
  logarithmic-time prefix-moment evaluator, the strict-negative-half
  conjecture, and the factor table through m = 31.
- `thue_morse_diagonal_polynomials_article_and_code/` — *Diagonal
  Polynomials and Dyadic Block Geometry in Repeated Thue–Morse Prefix
  Summation: Exact formulas, denominator laws, rational roots, and fast
  Wolfram Language evaluation* (33 pp). Contributed the root moments and
  root product, the diagonal Mahler equation, the half-grid transposition
  theorem, the complete description of the nonnegative rational roots, the
  trailing-ones family of negative integer roots, the exact row–histogram
  identification with the Rvachev approximants, and the formula sheet.

The three source directories were deleted when this volume was filed; Git
history retains them. Every shared result is stated once, in the form with
the most complete proof; the appendix *Source provenance* records which
report contributed each retained chapter, the notation dictionary between
the three reports, and the cross-checks performed before deduplication (no
discrepancy was found among the three).

## Contents

1. Problem, conventions, and main answer
2. Signed Thue–Morse prefixes and formal products
3. Generating function of the complete two-dimensional table (row and
   bivariate generating functions, the local discrete equation)
4. Why fixed-index iterated sums are polynomials (general summation-order
   and deflation theorems)
5. Riordan-array structure and a general subdiagonal theorem
6. The diagonal polynomials (sparse formula, monomial coefficients, root
   moments, fixed-diagonal asymptotics, finite-product forms, binomial
   basis)
7. Sheffer structure and efficient recurrences (half-step, ruler/Bell,
   partition and determinant forms, translation, differential and addition
   laws, the diagonal Mahler equation)
8. Exact denominators, primitive normalization, and rational zeros
9. Exact half-integer roots and factor patterns (transposition, complete
   nonnegative criterion, negative half-lattice, valuation criteria,
   trailing-ones family, the strict-negative-half conjecture)
10. Finite dyadic blocks for arbitrary summation order (complete
    finite-block theorem, moments of the block)
11. Specialization to the rows of the table
12. Connection with the Fabius and Rvachev approximation layer
13. Algorithms and Wolfram Language implementation
14. Computational verification
15. Further deductions and research directions, with formalization targets

Appendices: theorem dictionary; nonnegative rational factors through
m = 31; formula sheet for implementation; source provenance, notation
dictionary, and reproducibility.

## Files

- `Thue_Morse_Diagonal_Laws.tex`, `Thue_Morse_Diagonal_Laws.pdf` — the
  volume. It loads `docs/fabius-notation.tex` by relative path; build with
  three passes of `pdflatex -interaction=nonstopmode -halt-on-error`.
- `figures/` — the two profile figures used in the text (row profiles from
  the first report, normalized pulses from the third).
- `verification/source1/` — `experiments.py`, `thue_morse_table.wl`,
  `verification_report.txt`, `row_profiles.pdf/png` (first report).
- `verification/source2/` — `diagonal_polynomials.py`,
  `diagonal_polynomials.wl`, `VERIFICATION.txt` (second report).
- `verification/source3/` — `diagonal_analysis.py`,
  `thue_morse_diagonals.wl`, `generated/` (third report).

All verification programs are retained unchanged from the sources and were
not re-run for this consolidation. No Lean formalization is claimed for any
result in the volume; Chapter 15 lists the formalization targets in
dependency order.
