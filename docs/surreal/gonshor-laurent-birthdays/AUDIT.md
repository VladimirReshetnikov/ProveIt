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
   The 22 September 2026 review also checked the pinned
   [Bournez–Guilmant v1](https://arxiv.org/pdf/2201.08199v1), Definition 2.20
   and Theorem 2.21 on page 13. The former article citations to Definition 2.6
   and Theorem 2.7 were incorrect for that version and have been corrected.
   The block lengths, both deletion rules, and the prefix consequence agree
   with [Ehrlich's Propositions 3.7–3.8](https://math.hawaii.edu/home/jla/88-275-1-PB.pdf).
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

## Proof review, 22 September 2026

The mathematical review followed the dependency chain above: the additive
bound, real birthdays and scalar products, ordinal-exponent finite sums,
negative-exponent block induction, exact finite splitting, bounded and cross
products (including the sharp `d = M = 1` case), strictness, formal inversion,
infinite birthdays, finite-jet transfer, reciprocal corollary and spectrum.
No false theorem statement was found in that chain.

The exposition now states explicitly that birthdays belong to canonical
values, rather than arbitrary cut forms. Prefix comparisons in the deletion
rules use the original exponent sequences, and the second rule applies at
successor term indices. Counts of plus signs are ordinal order types.

The proof now isolates the unique extreme convolution pairs. Highest
exponents add for nonzero Laurent series; when both supports are finite,
lowest exponents and support widths add as well. This supplies the
noncancellation step used in the reciprocal argument. Interior coefficients
may cancel, and the finite-jet equality includes those zeros. The infinite
birthday proof displays cofinal lower and upper bounds and uses continuity
only of ordinary ordinal addition in the right argument.

The reciprocal hypothesis is illustrated by
`f = omega^(-2)-omega^(-3)`: its inverse has birthday `omega^2 * 2`, so the
bounded-reciprocal conclusion does not extend to every negative leading
exponent. These changes preserve the mathematical scope and make no novelty
claim. Historical verification code, recorded results, and layout audit are
unchanged.

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

The original PDF was compiled with pdfLaTeX through repeated passes until
references stabilized, with no undefined references, missing citations,
Overfull/Underfull box warnings, or LaTeX errors. Its pages were rendered and
reviewed as contact sheets; the original automated span checks remain in
`layout_audit.json`.

For the 22 September revision, clean three-pass baseline and revised builds
again produced no warnings or errors. The revised PDF has 21 pages, and the
changed proof, convention, and example pages were rendered and inspected.
The original layout JSON was preserved as a historical record and does not
describe the revised pagination. The existing quick verification command
also passed, writing its output only to a temporary directory. These finite
and layout checks are separate from the mathematical review above.
