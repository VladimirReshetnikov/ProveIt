# Claims ledger

## Analytic claims proved in the manuscript

- **Theorem 5.1:** a fixed Gaussian reporting advantage, together with an
  explicit transfer tolerance, yields a single batch size valid for every
  recursion depth. The standardized fourth moment stays at most eight.
- **Lemma 4.2:** a discontinuous quadratic reporting test with boundary in H
  coordinate hyperplanes has an explicit Wasserstein transfer bound. Applied
  after averaging, the bound is `64 M (Hq)^(1/4) ell^(-1/8)`.
- **Propositions 6.3 and 6.4:** the rational-threshold Gaussian gate and its
  symbolic batch size meet every required inequality.
- **Theorem 1.1:** the resulting balanced Boolean family has the explicit
  degree, dimension, and singleton-sum bounds displayed in the article.
- **Corollary 1.2:** the dimension exponent can be made arbitrarily close
  to one, at the cost of shrinking the strictly positive Fourier exponent
  improvement.

These are ordinary mathematical proofs, not peer-reviewed or formally
verified proof-assistant results.

## Finite claims checked exactly

- 20-bit example: 622 cells; maximum cell degree 16.
- Retained variance: `16 + 9/34816`.
- Exceptional probability, mean, variance: `17/2048`, `-31/17`, `1147/289`.
- Sign-readout degree and singleton sum: `16`, `6435/2048`.
- Every pointwise cancellation identity on the 3,125 block-sum states.
- All symmetry-reduced Fourier coefficients for the exceptional cell and
  the sign readout, plus one ordinary cell attaining degree 16.
- Every one of 11,726 distinct-singleton binomial rules in the stated finite
  parameter range; width four is the first positive row in that family.
- Rational numerical inequalities supporting the explicit Gaussian proof.

## Inherited ideas, with attribution

The low-degree observation framework and the exceptional reporting
cancellation are from the inspected OpenAI preprint. They are restated
and reproved. The Stein-equation derivative bound is standard and cited to
Ross. The historical conjecture is cited to O'Donnell's 2012 problem list.

## Consequences not claimed as the main novelty

Qualitative power-law growth above the square-root scale follows from the
source's unbounded-ratio assertion using one-bit oddization and balanced
composition. Proposition 8.2 explicitly explains this. The paper does not
present that deduction alone as a major new result.

## Claims NOT made

- No first-in-the-literature priority claim.
- No practical evaluation algorithm for the asymptotic family.
- No numerically competitive Fourier exponent.
- No claim that the 20-bit sign readout violates the square-root bound.
- No claim that the finite witness automatically amplifies indefinitely.
- No global minimality claim for 20 bits or cell degree 16.
- No numerical construction of the enormous Gaussian grid or averaging batch.
- No assertion that the entire openai/math repository has been verified.
- No Lean or other proof-assistant certification of these analytic results.
