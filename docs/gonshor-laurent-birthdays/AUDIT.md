# Mathematical and computational audit

## Research status

The selected problem is Gonshor's birthday product conjecture, not another
conjecture bearing Gonshor's name. The original question is documented on
p. 96 of his 1986 book and in van den Dries and Ehrlich (2001). Philip Ehrlich's
August 2024 MathOverflow answer reports the affirmative monomial case as the
strongest such result known to him. Searches on 20 September 2026 did not
locate a general resolution. They do not certify global absence of later work,
and did not establish novelty of the specific Laurent-series restriction.

## External mathematical inputs

1. The surreal normal-form theorem and compatibility with Hahn arithmetic.
2. Gonshor's sign-expansion theorem, including both minus-deletion rules.
   The exact statement was checked in Philip Ehrlich, Journal of Logic &
   Analysis 3:1 (2011), Proposition 3.7, pp. 10-11; Proposition 3.8 and
   Proposition 3.6(iii) also state the normal-prefix property. The relevant
   PDF pages were viewed, not only searched through extracted text.
3. The standard recursive cut/simplicity framework for the additive bound.

The known general monomial product theorem is cited for context, not assumed
as a missing step in the Laurent proof. Real scalar products are handled by
an elementary independent lemma. The 2001 paper's erratum is identified
bibliographically; none of the support-monoid, inversion, or exponential-field
estimates for which that broader work is relevant is used in this proof.

## Internally established chain

Real scalar birthday bound
  -> ordinal-exponent polynomial formula and product estimate.

Sign-expansion rule for integer exponents
  -> reduced negative-exponent block formula
  -> exact finite Laurent birthday formula
  -> exact positive/bounded natural-sum splitting
  -> bounded product estimate and positive-monomial cross estimate
  -> finite Laurent product theorem.

Normal-form prefix property + finite coefficient stabilization
  -> transfer of a fixed birthday product bound to infinite Laurent series.

Finite Laurent formula + prefix-union length
  -> infinite birthday formula
  -> bounded reciprocal formula and full birthday spectrum.

## Edge cases explicitly covered

- Zero factors and coefficients; absent coefficients are treated as dyadic zero.
- Negative real coefficients, which reverse signs without changing lengths.
- Nondyadic real coefficients, including irrational ones, have birthday omega.
- The additional minus deletion after a nondyadic preceding coefficient.
- An adjacent last exponent versus a gap of two or more exponents.
- Dyadic scaling that turns a nondyadic coefficient into a dyadic one.
- The cross-product case where both finite leading coefficients of the ordinal
  bound equal one; it is proved separately, not absorbed into a coarse estimate.
- Products with support collisions, coefficient cancellation, or finite support
  despite both inputs having infinite support.
- Infinite ordinary-ordinal absorption: the finite splitting identity is NOT
  asserted for infinite tails.
- No preservation of suprema by natural multiplication is assumed.
- The entire infinite argument uses one fixed upper bound B, not a limiting
  equality for natural operations.

## Computation

The full `verify.py` run completed successfully; its actual machine output
is `verification_results.json`. It performs finite exact-rational tests only.
The closed Laurent formula and general sign-expansion implementation are
separate code paths. They share basic ordinal arithmetic, not the asserted
closed birthday formula. This is useful cross-checking, not full independent
formal verification.

There is no Lean/Coq/Isabelle certification, no quantification over all real
coefficients by the program, and no computational verification of infinite
series. Those cases are addressed by the written proofs.

## Limits of the result

The work does not settle Gonshor's conjecture for arbitrary surreal exponents
or arbitrary reverse-well-ordered supports. The random dyadic-exponent search
found no counterexample but does not prove even that finite-support extension.
The absence of a counterexample is not promoted to a universal theorem.

## PDF checks

The PDF was compiled with pdfLaTeX through repeated passes until references
stabilized. The final log had no undefined references, missing citations,
Overfull/Underfull box warnings, or LaTeX errors. All pages were rendered and
reviewed as contact sheets; proof and final-reference pages were additionally
viewed at a larger scale. Automated final-page span checks are included in
`layout_audit.json`. These are layout checks, not mathematical proof checks.
