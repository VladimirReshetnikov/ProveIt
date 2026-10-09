# Sharp and Computable Corrections for Nonuniform Coupon Collection

Research package prepared for Vladimir Reshetnikov, 8 October 2026.

The complete article is **article/coupon_collector.pdf**; its editable
source is **article/coupon_collector.tex**. The ZIP includes the bibliography,
figure assets, a certified numerical implementation, independent tests, and
all recorded experiments.

## The result

For independent observations in categories with probabilities \(p_i\), let
\(P_m\) be the probability that every category has appeared after \(m\)
observations. Define

\[
F(t)=\prod_i(1-e^{-tp_i}),\qquad
M_k(t)=\sum_{A\subseteq[n]}p_A^k e^{-tp_A}.
\]

Let \(c_k(m)=[x^k](1-x)^m e^{mx}\), and let the order-\(s\) approximation be

\[
A_s(m)=\sum_{k=0}^{2s-1}(-1)^k c_k(m)F^{(k)}(m).
\]

The article proves an explicit positive radius

\[
R_s(m)=B_{m,s}M_{2s}(m)+
\frac{\binom ms}{2^s}
\sum_{\ell=0}^s\binom s\ell M_{2s+\ell}(m)
\]

such that \(|P_m-A_s(m)|\le R_s(m)\) for every probability vector and all
positive integers \(m,s\). The constants \(B_{m,s}\) are explicitly
computed rational combinations of binomial coefficients. The apparent
subset sums are evaluated through truncated products.

The precise pointwise comparison is to Hwang, Li, and Zacharovas,
arXiv:2605.29633v1, Lemma 5.3. The new upper-bound function is strictly
smaller for every \(x>0\) on the same domain. For order one, their stronger
Lemma 2.1 is also acknowledged and improved.

The article additionally proves:

- The best scalar remainder constant is
  \[
  K_{m,s}=\frac{m^s}{2^ss!}
  \left(1+\frac{s(-2s^2+5s+1)}{9m}+O_s(m^{-2})\right).
  \]
- Its global maximizing argument is unique for sufficiently large \(m\)
  at fixed \(s\), and equals \(2s(s+1)/(3m)+O_s(m^{-2})\).
- The optimal constant and maximizing argument have convergent expansions
  in \(1/m\) near infinity at fixed order.
- The first-order constant also satisfies the all-\(m\) bound
  \(K_{m,1}\le m^2/(2m-1)\).
- A rare-coupon family attains the leading constant in the positive radius.
- Uniformly over arbitrary probability vectors with
  \(\sum_i e^{-mp_i}\le L\), the error is
  \(O_{L,s}((\log n/n)^s)\), with an explicit finite envelope.
  The rate of this truncation is sharp for every fixed \(L>0\).

## What is established prior work

The Poisson–Charlier expansion, high-order uniform coupon approximations,
and elementary depoissonization methods are prior work. The contribution
here is a concrete remainder refinement, its sharp scalar analysis, and
its constructive use for certified probabilities. The article identifies
the exact earlier lemma being strengthened and distinguishes the
33-based unsigned majorant from the stronger cancellation-aware seminorm
in Zacharovas's general theorem.

This is not a claim to have solved a longstanding major conjecture.
The proofs are included, but the manuscript is an AI-assisted research
draft and has not undergone external peer review or proof-assistant
formalization. Novelty beyond the stated direct comparison has not been
certified by an exhaustive literature review.

## Installation

Python 3.11 or later is needed for the pinned experiment dependencies;
the core calculation supports Python 3.10. The recorded run used
Python 3.12.14.

~~~bash
python -m pip install -r requirements.txt
~~~

Only python-flint is required for the core probability calculation.
The remaining dependencies reproduce plots and symbolic experiments.

## Compute a certified probability

~~~bash
python src/coupon_certificate.py --uniform 10000 \
    --m 99034 --order 4 --bits 224

python src/coupon_certificate.py --weights 1,2,3,5 \
    --m 100 --order 3 --bits 160
~~~

Weights are normalized exactly. Use integers, rational strings such as
"3/7", or decimal strings such as "0.1". Binary floating-point weights
are deliberately rejected. A JSON input file can contain a list of those
integers or strings:

~~~bash
python src/coupon_certificate.py --weights-json probabilities.json \
    --m 1000 --order 3 --bits 160
~~~

The returned **enclosure**, intersected with [0,1], contains the true
probability, including both analytic and rounding errors. The field
**analytic_radius** is the unified \(R_s\) in the article. The optional
first-order scalar refinement is stated mathematically in the article;
the implementation and comparison tables use the same unified \(R_s\)
at every order.

Do not treat a printed floating-point midpoint as an interval. The JSON
uses Arb real-ball strings; plotting data additionally contain explicitly
labeled approximate midpoints.

## Reproduce the checks

~~~bash
python -m unittest discover -s tests -v
python experiments/run_experiments.py
python experiments/sharp_scalar.py
~~~

The independent test suite checks exact rational probabilities using
integer inclusion–exclusion and occupancy recurrences. The experiment
program checks complete 320-bit grouped inclusion–exclusion references
against 224-bit probability certificates. The scalar program checks
symbolic coefficient identities and high-precision stationary points.
Root-finding experiments are not used as proofs of global optimality.

The recorded run passed all 11 test methods and all 68 reference-interval
containment checks. Data are in **results/**, and plots are in **figures/**.
Re-running the experiments replaces these generated results and records
the new environment and timings.

## Build the article

A TeX installation with latexmk, pdfLaTeX, BibTeX, and the standard
packages listed in the preamble is required.

~~~bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
    -cd article/coupon_collector.tex
~~~

The bibliography and the figure directory must accompany the TeX file.
They are all included in this ZIP.

## Interpretation and limits

The product work is \(O(ns^2)\), with \(O(s^3)\) cached rational setup and
\(n\) exponential evaluations. This is an arithmetic-operation count;
input bit length and requested precision still matter. All asymptotic
statements fix \(s\). The certificate is additive and can be wide early
in the process. More working precision reduces rounding uncertainty, not
the analytic remainder. More correction terms need not monotonically
improve every finite input.

The 100,000-category timings are single measurements, with equal-weight
grouping disabled, not statistical benchmark estimates. For the
10,000-category uniform example, the order-four certified radius is
approximately \(1.226568\cdot10^{-12}\), and the independently computed
absolute error is approximately \(1.833985\cdot10^{-14}\).

## File map

| Directory or file | Contents |
|---|---|
| article/ | Complete manuscript, PDF, and primary-source bibliography |
| src/coupon_certificate.py | Certified Arb implementation |
| tests/test_certificate.py | Exact and independent verification |
| experiments/run_experiments.py | Probability, sharpness, and timing experiments |
| experiments/sharp_scalar.py | Symbolic and numerical scalar checks |
| results/ | JSON, CSV, figure captions, and numerical provenance |
| figures/ | Vector PDF and raster PNG figures |
| VERIFICATION.md | Scope and outcome of the validation |
| provenance.json | Repository snapshot and source versions |
| SHA256SUMS.txt | Checksums of packaged files |

Further research questions are developed in the article: finite optimal
constants, growing order, cancellation-sensitive radii, relative error,
heterogeneous quotas, bit complexity, quantiles, and formal verification.
