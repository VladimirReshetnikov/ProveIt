# The Lower Critical Endpoint
## Arbitrary-Rate Condensation, Cauchy Cutoff Laws, and Degenerating Transseries

A 25-page research article (24 pages as delivered) prepared for Vladimir Reshetnikov, 29 September 2026.

## Files

- `lower_critical_endpoint.pdf`: compiled article.
- `lower_critical_endpoint.tex`: self-contained LaTeX source; the numerical tables are embedded.
- `verify.py`: exact finite algebra checks and floating-point numerical diagnostics.
- `verification_results.json`: complete recorded results of the full verification run.
- `verification_run.txt`: human-readable console output from that run.
- `requirements.txt`: dependencies for the verification program.
- `build.sh`: three-pass PDF build.
- `SOURCE_NOTES.md`: pinned repository provenance, literature, scope, and novelty boundaries.
- `VALIDATION.md`: compilation, mathematical-proof checks, and computational-validation boundaries.

## Research target

The paper addresses the lower-endpoint half of Question 4 in ProveIt's
`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex`, at commit
`3d5973524506411392a911470b5ddc35521568ea`.

The family is

    U(q) = c_epsilon [Li_(2+epsilon)(q exp(U(q))) + P(q exp(U(q)))],
    c_epsilon = 1 / (zeta(1+epsilon) + P'(1)),

where P is a fixed polynomial that alters finitely many nonnegative action
weights. The parameter epsilon tends to zero while the coefficient index n
tends to infinity.

## Main conclusions

The article proves a coefficient equivalent for **every** rate epsilon_n -> 0,
including nc_epsilon tending to infinity, remaining bounded, or tending to zero.
For rho = exp[-c_epsilon(zeta(2+epsilon)+P(1))] and

    d = (n c_epsilon / epsilon)^(1/(1+epsilon)),

it gives

    [q^n]U(q) ~ rho^(-n) epsilon/(n d).

The probability configuration producing the coefficient has one exceptional
action. Deleting that largest action recovers the unconditioned Poisson
configuration in total variation. In the dense regime the remaining actions
have a compensated, right-skewed 1-stable cloud on the smaller scale

    b = (n c_epsilon)^(1/(1+epsilon)).

For a prescribed retained fraction r, the smallest action cutoff is

    M_r = d + b [log(1/epsilon)/(1+epsilon) + F^(-1)(r)] + o(b),

where F is the explicitly normalized reflected 1-stable distribution in the
paper. Omitting the logarithmic shift causes asymptotically zero retention,
even though the leading relative scale is correct.

A separate convergent critical inverse chart is uniform through the removable
parameter endpoint. The endpoint equation itself degenerates to U=0; the paper
does not misidentify that endpoint as a nonzero critical solution.

## Proof and novelty status

These are conventional proofs in an unrefereed research article. General
one-large-summand principles, Cauchy condensation, and largest-summand deletion
are credited to the existing literature. The scoped contribution is the
explicit arbitrary-rate triangular-family theorem and its consequences here.
Global publication priority has not been established.

There is no new Lean formalization and no claim to solve general resurgence,
Borel summability, arbitrary slowly varying tails, or every lower-endpoint
transseries model. The formalization plan and nine further research directions
are in the article. No repository files were modified.

## Build

With a standard TeX installation including the packages listed in the source:

    sh build.sh

Alternatively run `pdflatex lower_critical_endpoint.tex` three times.

## Verification

With Python 3.10 or later:

    python -m pip install -r requirements.txt
    python verify.py

The full run writes `build/verification_results.json`. A shorter run,

    python verify.py --quick

writes `build/verification_quick.json` instead. Neither replaces the recorded
`verification_results.json`, which only `--overwrite-recorded` may write (as
delivered, the full run wrote over it; see the amendments below).

The recorded run passed **62 exact algebra assertions**. The coefficient,
cutoff, chart, finite-prefix, and CDF calculations are floating-point diagnostics,
not interval certificates. The full run uses extended-precision long-double
recurrences where supported and checks for underflow. The mathematical proofs
do not depend on these numerical calculations.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 52 (see `docs/incoming/README.md`). The
following changes were made on 2026-09-29; everything else is as delivered.

- `lower_critical_endpoint.tex`: an unnumbered `ednote` environment (the
  article's remarks share the theorem counter, so its numbering is
  unchanged) and five visible "Editorial note (ProveIt, 2026-09-29)"
  paragraphs, each preceded by a `% ed. (2026-09-29)` comment:
  - end of Section 1.1: the problem is resolved on the boundary-critical path
    only (the subcritical side and a coupling window stay open); the same
    question is Question 10 of
    `../Confluent_Critical_Transseries_Exponent_Two_Boundary/` (coupling
    `1/zeta(alpha)`, the case `P = 0`) and Question 8 of
    `../Logarithmic_Critical_Endpoint_Lambert_Charts/`, answered on this path
    by `D_n`, `b_n`, Theorem 3.1(a) (one exceptional action),
    `lambda = n c_eps`, the chart and the budget; the interior-fold side is
    `../Lower_Critical_Endpoint_Landau_Transseries/` (batch 51); the cited
    lines 1502-1507 of the critical Hahn article were 1509-1514 on filing;
  - after Corollary 10.1 (`cor:hahncoefficient`): `H_n` is the critical Hahn
    article's `eq:critical-leading` (`thm:phases`) with `a = 1`,
    `beta = c_eps`, `B = c_eps Gamma(-1-eps)`, so the corollary proves that
    fixed-`alpha` law uniformly as `alpha -> 1`; that article's `b_n` is
    asymptotic to `d_n` here;
  - end of Section 10.4: the independent batch-52 package
    `../Lower_Critical_Endpoint_Uniform_Coefficients_Compound_Poisson/` treats
    the same family at the same pin. One theorem with two independent proofs:
    its `B` satisfies `B/d_n -> 1`, `eps B/b_n -> 1`,
    `B + eps B log(1/eps) = D_n - (1-gamma) b_n + o(b_n)`, and its standard
    Landau variable is `Z - (1-gamma)`, so the cutoff quantiles coincide; it
    adds a quantitative uniform error, all fixed orders and the first
    correction, which reproduces the gamma-ratio column of Table 1 to three
    or four digits; it does not claim the joint cloud-extremes limit proved
    here. These identities were checked on filing;
  - at research question 2: partly answered by that package
    (`thm:uniform`, `thm:allorders`, `cor:first`);
  - Appendix (reproduction): the new default output location and the
    Windows `longdouble`.
- `lower_critical_endpoint.pdf`: rebuilt from the amended source with
  `latexmk -pdf` (25 pages; the delivered PDF had 24; no errors, undefined
  references, multiply defined labels, duplicate destinations or overfull
  boxes). Line numbers of the source after line 29 differ from the
  delivered file. `VALIDATION.md` (24 pages) describes the delivered build.
- `verify.py`: as delivered, the full run always rewrote the recorded
  `verification_results.json` beside the script. It now has `--output`,
  defaulting to `build/verification_results.json` (or
  `build/verification_quick.json` with `--quick`), and refuses to write the
  recorded file without `--overwrite-recorded`. It already wrote LF.
- Rerun on a copy (Windows, Python 3.13.5, mpmath 1.3.0, SymPy 1.14.0,
  NumPy 2.3.5, SciPy 1.17.0, default output): 62 exact assertions passed.
  NumPy's `longdouble` on Windows has 53 bits, not the recorded 64, so the
  output records `long_double_bits` 53; every other number agrees with the
  record to a relative 1e-13, except the quadrature's own error estimate
  for one CDF value (7.64e-12 in both, differing in the sixth digit).
- `build.sh` runs pdfLaTeX in this directory and leaves `build-pass-N.log`
  and auxiliary files here (ignored by the repository).
