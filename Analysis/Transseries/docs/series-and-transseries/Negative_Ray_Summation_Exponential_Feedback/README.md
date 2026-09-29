# Negative-Ray Summation of Countable Exponential-Feedback Transseries

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Main result

For nonnegative finite real slopes in

    U(q) = sum_{j>=1} q^j exp(lambda_j U(q)),  Q = compositional_inverse(U),

the following are equivalent:

- lambda_j = O((j log(j+1))^2);
- U is Gevrey-1;
- Q is Gevrey-1;
- U is finely Borel-Laplace summable on the negative ray;
- Q is finely Borel-Laplace summable on the negative ray.

The summed functions are inverses and recover the literal, convergent feedback
kernel near the negative real axis. “Fine” means analytic continuation and an
exponential bound in a fixed-width tube around the ray, not an open angular
sector. The article proves the required nonlinear inverse closure for that
half-strip setting.

The proof gives a signed inverse exponential-block expansion and a Bessel-kernel
Borel representation. If A = limsup lambda_j/(j log j)^2 is finite and positive,
the inverse Borel transform is analytic in |zeta| + Re(zeta) < 1/(2A). If A=0,
it is entire. This is a guaranteed domain, not a maximal-domain claim.

For lambda_j=j^2, P(u)=exp(u) Q(u) has a uniform closed-left-half-disc remainder
bound r^N M_N, where M_N is explicit and

    log M_N = N log N - 2 N log log N + (log 4 - 1) N + o(N).

Choosing N ~ log(1/r)^2/(4r) gives an error upper bound
exp[-(1/4-o(1)) log(1/r)^2/r]. The asymptotic is sharp for the positive
majorant, not asserted to be sharp for the actual signed truncation error.

## Relationship to earlier repository work

The source snapshot is a795fcffa4b3ece22761d81fbed3c43be8b81795.
The direct predecessor is the package Exponential_Feedback_Regularity_Classification
under Analysis/Transseries/docs/series-and-transseries/. That package already
contains the coefficient/Gevrey classification, a positive-ray Borel obstruction,
and a Poincare left-sector realization. The present proposed contribution is the
negative-direction fine summation theorem and the quantitative uniform remainder
and certificate theory. The classification is not presented as newly discovered.

The source review was targeted, not an exhaustive audit of the entire canonical
transseries volume. See SOURCES.md.

## Contents

- article.tex: self-contained source, with bibliography.
- article.pdf: compiled A4 article.
- code/verify.py: independent forward recurrence and inverse-block construction;
  exact composition checks; rational function-value and inverse-error certificates;
  optional mpmath diagnostics.
- code/majorant.py: non-certified floating-point majorant/saddle diagnostics.
- data/coefficients.csv: exact U, P, Q, and mass coefficients through degree 24.
- data/quadratic_blocks.json: exact signed block polynomials through block 24.
- data/rational_certificates.json: three exact rational enclosures of Q(-r).
- data/inverse_certificate.json: exact residual-transport enclosure of U(-1/40).
- data/verification.json: recorded exact-check results and separate numerical checks.
- data/majorant_diagnostics.csv: positive-majorant diagnostics through N=100000.
- data/build_validation.json: PDF build and page-boundary checks.
- requirements.txt: optional numerical dependency.
- Makefile: local build/check commands.
- SOURCES.md: provenance, primary references, and scope of novelty review.

## Reproduce

Use Python 3.10+ and a TeX Live installation containing the standard mathematics
packages used in the preamble. The recorded run used Python 3.13.5 and mpmath 1.3.0.

    python -m pip install -r requirements.txt
    python code/verify.py --order 24
    python code/majorant.py
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

Alternatively: `make check`, `make diagnostics`, and `make pdf`.
Exact checks run without mpmath; numerical diagnostics are then marked not run.
The programs do not access the network or modify the upstream repository.

## Verification and limits

Both inverse compositions were checked exactly through degree 24. The mass
recurrence, block support/mass bounds, and zero/linear slope cases also passed.
Three Q-value enclosures and one U-value enclosure were calculated using exact
rational arithmetic and proved bounds. Their terminating decimal endpoints are
outward-rounded rationals, not floating-point assertions.

The 70-digit numerical root comparisons and four Bessel-Laplace integral checks
are explicitly non-certified diagnostics. The majorant diagnostic is also not
interval arithmetic; its slow approach to the asymptotic constant should not be
used in place of the finite bound.

The theorems are conventional proofs, not Lean-verified results. No peer review
or global publication-priority claim is represented. The article does not claim
angular summability, a maximal Borel domain, a general resurgence theorem, or a
matching lower bound for the actual least truncation error. Eight further
research questions and a staged formalization roadmap are included.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 47 (see `docs/incoming/README.md`). The
following changes were made after filing; everything else is as delivered.

- `article.tex`: an unnumbered "Editorial note (ProveIt, 2026-09-29)"
  environment was added to the preamble. Editorial notes were added
  (1) after the author's remark following Theorem 2.6 (`thm:optimal`): despite
  its label, the theorem is an upper bound from the majorant, not a sharp
  optimal-truncation result, with the related scales of the later
  microscopic-condensation (forward least term) and sectorial-summability
  (actual error, unspecified constant) packages; (2) after the question
  "Angular summability of the quadratic model": answered negatively for
  `lambda_j = j^2`, and for rational amplitudes with eventually quadratic
  slopes, by the later natural-boundaries package; (3) after "The actual
  Borel boundary at critical slope growth": the type part is answered by the
  weighted-type package (`T_s(Q) = T_s(U)`, exact Borel radius `1/(4A)`), and
  the note records the editorial deduction that the parabola's vertex
  `zeta = 1/(4A)` is then a singular point for `0 < A < oo`; (4) after "Signed
  coefficient asymptotics and actual least error": the coefficient part is
  claimed by the two batch-49 quadratic-inverse packages (not reviewed); the
  least-error part stays open. Every change is marked in the source by a
  `% ed. (2026-09-29)` comment. No label, theorem or number changed.
- `article.pdf`: rebuilt from the amended source (24 pages; the delivered PDF
  had 23). `data/build_validation.json` describes the delivered build and was
  not updated.
- `code/verify.py`, `code/majorant.py`: every writer emits LF line endings on
  every platform (the delivered `majorant.py` wrote CR CR LF on Windows). A
  rerun on a copy (`verify.py --order 24`, `majorant.py`) reproduced all six
  written `data/` files byte for byte. The programs rewrite the recorded
  `data/` files in place; run them on a copy.
