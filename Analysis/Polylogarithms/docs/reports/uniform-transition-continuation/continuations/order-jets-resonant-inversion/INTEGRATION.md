# Integration notes: Polylogarithm Order Jets and Resonant Inversion

## Status and provenance

This package is a standalone research contribution prepared against ProveIt revision
`9ec0f0406afe7a5475b03ff65ed91f7e283979b8`. The repository snapshot was inspected
read-only. No repository file was changed, committed, or pushed while preparing
the report. The paths below refer to that pinned revision; later repository
changes must be reconciled before integration.

The paper supplies conventional mathematical proofs and supporting verification
programs. It contains no Lean formalization. Publication priority is not claimed.
See [CLAIMS.md](CLAIMS.md) for the statement-level scope and limitations.

## Proposed canonical destination

Use one canonical report directory:

`Analysis/Polylogarithms/docs/reports/order-jets-resonant-inversion/`

Retain the standalone TeX source, compiled PDF, build instructions, verification
programs, executed JSON results, and these integration notes together. Link to
that report from the transseries inventory rather than maintaining two copies of
the complete source. The destination is a proposal for later manual integration;
this package does not create it in ProveIt.

Suggested index and editorial updates, after review:

1. Add an entry to `Analysis/Polylogarithms/README.md` under research reports or
   the closest existing heading.
2. Add a crosslink in
   `Analysis/Transseries/docs/series-and-transseries/README.md`, identifying the
   higher-logarithmic-degree inverse chart, complex spectral folds, and exact
   integer-order exponential inverse expansion.
3. In the predecessor resonance report's R1, record a scoped resolution by the
   new complex-sector theorem. Preserve R3 on growing jet order and R4 on general
   growing transition windows as open; this paper does not settle them in full.
4. Add a cross-reference after the predecessor single-logarithm Lambert chart
   pointing to the present higher-degree coefficient and sharp-pole theorems.
   The existing theorem remains valid and should retain its original attribution.
5. If the work is later incorporated into the collective manuscript, record its
   arrival in the existing editorial ledger before copying individual sections.
   Preserve one authoritative version of each theorem and its hypotheses.

An optional short index description is:

> Polylogarithm order jets and resonant inversion: finite Gamma normalization to
> pure logarithmic normal forms; convergent Lambert-coordinate inverses with
> explicit coefficient poles; complex critical-value accumulation and spectral
> folds; exact order-jet reconstruction of exponential sectors at large negative
> argument. Conventional proofs with finite symbolic and numerical verification.

## Pinned predecessors and precise increments

### P1. Uniform integer-order Lerch resonance

Exact source:

`Analysis/Polylogarithms/docs/reports/uniform-transition-continuation/continuations/resonance-correlations-nonseparable-jets/sections/02_resonance.tex`

[Pinned source](https://github.com/VladimirReshetnikov/ProveIt/blob/9ec0f0406afe7a5475b03ff65ed91f7e283979b8/Analysis/Polylogarithms/docs/reports/uniform-transition-continuation/continuations/resonance-correlations-nonseparable-jets/sections/02_resonance.tex)

The relevant labels are `res:exact` (pole-paired identity), `res:main` (uniform
real-argument resonance), `res:highorder` (limiting coefficient function), and
`res:finitepart` (fixed-order Stieltjes finite parts). The present paper attributes
these inputs. Its `thm:sector` extends the forward theorem to a fixed complex
logarithm sheet and closed sectors, with the same uniformity in the integer
order. Its `thm:purejet` then applies a finite reciprocal-Gamma transformation to
produce one pure logarithmic monomial plus a convergent analytic tail.

The explicit open question is R1 in:

`Analysis/Polylogarithms/docs/reports/uniform-transition-continuation/continuations/resonance-correlations-nonseparable-jets/sections/07_questions.tex`

[Pinned questions](https://github.com/VladimirReshetnikov/ProveIt/blob/9ec0f0406afe7a5475b03ff65ed91f7e283979b8/Analysis/Polylogarithms/docs/reports/uniform-transition-continuation/continuations/resonance-correlations-nonseparable-jets/sections/07_questions.tex)

R1 requests complex approach to the singular argument with a specified logarithm
and a uniform majorant. That is the specific repository question resolved here.

### P2. The single-logarithm Lambert chart

Exact source:

`Analysis/Transseries/docs/series-and-transseries/Logarithmic_Critical_Endpoint_Lambert_Charts/article.tex`

[Pinned source](https://github.com/VladimirReshetnikov/ProveIt/blob/9ec0f0406afe7a5475b03ff65ed91f7e283979b8/Analysis/Transseries/docs/series-and-transseries/Logarithmic_Critical_Endpoint_Lambert_Charts/article.tex)

The relevant labels are `thm:lambert`, `cor:criticalchart`, `prop:geometric`, and
`prop:ramification`. The predecessor treats
`y = B t^m(log(1/t)+h) + t^(m+1)R(t)` and gives a convergent correction about a
Lambert core. The new `thm:inverse` treats every integer logarithmic degree
`q >= 1` after Gamma normalization. The additional structural conclusions are
the support `V-1 in T eta^q C{T,eta}`, the explicit formula in
`thm:coefficients`, and the sharp order-`2n-1` poles with Catalan constants in
`thm:sharp-poles`. The implicit-function mechanism itself is inherited standard
analysis, not a new general inversion principle.

### P3. A confluent real critical chart

Exact source:

`Analysis/Transseries/docs/series-and-transseries/Confluent_Critical_Transseries_Exponent_Two_Boundary/Confluent_Critical_Transseries.tex`

[Pinned source](https://github.com/VladimirReshetnikov/ProveIt/blob/9ec0f0406afe7a5475b03ff65ed91f7e283979b8/Analysis/Transseries/docs/series-and-transseries/Confluent_Critical_Transseries_Exponent_Two_Boundary/Confluent_Critical_Transseries.tex)

The relevant labels are `prop:normal`, `thm:chart`, and `sec:future`, especially
future question 6 on complex continuation of the core. That report proves a
uniform real moving-exponent chart for a specified positive feedback model. The
present complex-resonance section instead studies the direct defect
`zeta(2+epsilon) - Li_(2+epsilon)(exp(-t))` near nonzero imaginary zeros of its
leading crossover profile. Its exponential critical lattice and exact spectral
fold are additions for this different model. They should not be recorded as a
complete solution of P3's broader complex-core question.

### P4. General analytic inverse transport

Exact source:

`Analysis/Transseries/docs/series-and-transseries/Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex`

[Pinned source](https://github.com/VladimirReshetnikov/ProveIt/blob/9ec0f0406afe7a5475b03ff65ed91f7e283979b8/Analysis/Transseries/docs/series-and-transseries/Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex)

The statement-level comparison concerns `thm:transport` and its analytic
Lagrange coefficient principle. The present integer-order Fermi--Dirac inverse
formula, `prop:borel-inverse`, specializes ordinary analytic inversion to a
known polynomial core and an explicitly convergent exponential completion.
Neither Lagrange inversion nor convergence of small analytic inverse
perturbations is claimed as new.

## Crosslinks within the new paper

| Topic | Main labels | Suggested connection |
|---|---|---|
| Uniform complex forward resonance | `thm:sector` | P1, R1 |
| Finite Gamma normalization | `thm:purejet`, `eq:finite-triangular` | P1 order derivatives and Stieltjes calculus |
| Higher-degree inverse and coefficient poles | `thm:inverse`, `thm:coefficients`, `thm:sharp-poles` | P2 |
| Critical lattice, local exhaustion, and principal-sheet restriction | `cx:critical-chart`, `cx:critical-lattice`, `cx:critical-exhaustion`, `cx:necessary-line` | Complex continuation and inverse branch geometry |
| Two-root resonance and transverse fold | `cx:split`, `cx:uniform-lattice-splitting`, `cx:eta-unfolding`, `cx:exact-fold` | Scoped comparison with P3 |
| Exact lateral completion and jet reconstruction | `thm:borel-exact`, `thm:borel-jet-reconstruction` | Attributed Fermi--Dirac and resurgence literature |
| Meromorphic first-order-jet kernel | `thm:borel-meromorphic-jet` | Order derivatives, pole residues, and exponential sectors |
| Integer-order exponential inverse | `prop:borel-inverse` | P4 and ordinary Lagrange inversion |

Use theorem labels or titles rather than temporary theorem numbers when moving
sections. The standalone paper reuses common labels such as `thm:inverse`; these
will need a report-specific prefix if inserted into a larger TeX compilation.

The critical-point exhaustion result removes an earlier draft's incomplete
classification caveat in the fixed sufficiently small purely imaginary order
regime. Do not leave that superseded caveat in a copied section or research
question. The common order-coordinate splitting chart also permits a growing
exact resonance index under its explicit small-coordinate conditions; it does
not settle general growing off-resonance windows.

## Corrections and preservation requirements

No new confirmed error was found in the directly used predecessor theorem
statements or proofs. This is a bounded audit, not a claim that the entire
repository is error-free. Earlier corrections already present in P1, including
the harmonic-sequence monotonicity and retention of finite-integer-order
coefficients, must not be presented as discoveries of this package.

An incorrect sentence in the new draft was corrected during preparation: a
nonzero linear leading term in the unsubtracted polylogarithm defect does not
make its inverse analytic at the endpoint. The inverse still has logarithmic
corrections. This was a correction to our draft, not to ProveIt.

The necessary-line theorem is also used to assess an explicitly cited external
heuristic draft. Preserve the source attribution and the fixed-order,
principal-sheet qualifications. Do not reclassify that external comparison as a
repository correction.

A second external correction concerns the finiteness summary in Cormac
O'Sullivan's *Zeros of the dilogarithm*, Section 8.1, printed page 18 of the
[author-hosted PDF dated 15 December 2014](https://fsw01.bcc.cuny.edu/cormac.osullivan/Research/dilog_zeros_final.pdf).
The overview's assertion of finitely many principal-branch zeros for every
complex order with `Re s > 0` is false as stated: `cx:critical-lattice` produces
infinitely many zeros at each sufficiently small fixed `s=1+i beta`, `beta != 0`.
These zeros lie inside the unit disk and accumulate at `z=1`, so changing
continuation conventions cannot remove the counterexample. Preserve this exact
scope when integrating the correction. The cited original Gawronski paper was
not inspected, and no error is attributed to its theorem. O'Sullivan's
positive-real-order zero theorem is unaffected.

Retain `verify_principal_sheet.py` and its executed `principal_sheet_check.json`
with the verification artifacts. This additional diagnostic computes a root
using the paired local chart and independently evaluates the positive-real Bose
integral. It records analytic cutoff bounds separately from uncertified
quadrature error. It supports branch bookkeeping; the article's analytic proof,
not the numerical residual, establishes the infinite sequence.

