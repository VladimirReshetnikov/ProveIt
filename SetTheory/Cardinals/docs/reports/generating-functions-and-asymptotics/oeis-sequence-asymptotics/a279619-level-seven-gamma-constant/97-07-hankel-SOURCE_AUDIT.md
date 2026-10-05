# Source and contribution audit

Date: 4 October 2026.

## Repository starting point

Repository: https://github.com/VladimirReshetnikov/ProveIt
Main-tree revision returned during inspection:
`a21208b3ff14a07a4c8318dbf916d543acbef043`.

Relevant directory:
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a279619-level-seven-gamma-constant/`

The directory's README describes a merged report titled *An Exact Gamma
Constant for an Apéry-like Sequence*, dated October 1 with a further derivation
added October 2. Its Section 13.13 incorporates manuscript 56, question R6,
which asks for global log-convexity or stronger total positivity and suggests
a Stieltjes-moment representation. The prior manuscript
*A279619_exact_asymptotics.tex* was also inspected through the user's Library.

The earlier report supplies the gamma evaluation
C=sqrt(3*pi)/(Gamma(1/7)Gamma(2/7)Gamma(4/7)) and the rational sequence
corrections. These are attributed as prior, unrefereed repository results.
This delivery independently proves existence, positivity, and all-orders
structure of the asymptotic constant directly from the recurrence, but does
not redo the gamma evaluation. The new positivity results do not require it.

## Primary external sources consulted

1. OEIS A279619: https://oeis.org/A279619
   Recurrence, initial values, and generating-function square relation.
   The square-sequence entry A183204 was also inspected as context.
2. Fallat, Johnson, Sokal, *Total positivity of sums, Hadamard products and
   Hadamard powers: Results and counterexamples*, corrected arXiv version:
   https://arxiv.org/html/1612.02210
   Especially Theorem 2.2 and Lemma 2.4 (strict contiguous-minor criteria).
   The report uses the strict criterion, not an uncorrected proof about
   nonnegative Hankel matrices elsewhere in that paper.
3. Hou and Zhang, *Asymptotic r-log-convexity and P-recursive sequences*,
   Journal of Symbolic Computation 93 (2019), 21–33:
   https://arxiv.org/abs/1609.07840
   https://doi.org/10.1016/j.jsc.2018.04.012
   Consulted for context; its iterated log-convexity is not confused with TP_r.
4. Mao and Pei, *The asymptotic log-convexity of Apéry-like numbers*,
   Journal of Difference Equations and Applications 29 (2023), 799–813:
   https://doi.org/10.1080/10236198.2023.2255308
   Publisher abstract and bibliographic data consulted for related work.

## New sequence-specific claims supported by this delivery

- An elementary all-index strict log-convexity proof.
- Global strict total positivity of order five, with complete exact
  coefficient certificates, including arbitrary noncontiguous minors.
- An exact order-six obstruction and a degree-five nonnegative-polynomial
  witness against a Stieltjes measure.
- Positive Stieltjes representability through degree ten, impossibility at
  degree eleven, and the exact minimum admissible repaired eleventh-degree
  moment (the twelfth sequence term), with an attaining spectral construction.
- Explicit fixed-order Hankel asymptotics, corrections, and inverse scales;
  eventual total positivity of each fixed order.

The coefficient generator, stable-ratio analysis, finite-difference method,
Schur complement, and finite spectral quadrature use classical mathematics.
They are supplied with proofs; they are not each asserted to be historically
new general tools.

## Search scope and unresolved claims

Targeted searches combined A279619 with Hankel, positivity, total positive,
and log-convexity, along with related searches on asymptotic positivity of
polynomial-recursive sequences. No inspected source stated the sharp order
classification or the exact moment repair. Search coverage is limited;
absence from these searches does not establish universal priority.

No positive Hamburger representation, a fixed Stieltjes-positive tail,
optimal thresholds beyond order five, or a growing-order asymptotic is
claimed. The finite sign data are expressly restricted to their tested
ranges. No OEIS submission or repository edit was performed.
