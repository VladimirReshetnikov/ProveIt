# Reciprocal Lerch Convolutions

**Entire-order identities, central-factorial zeta reductions, all logarithmic
moments, and Stieltjes–Gamma calculus.**

Research continuation for Vladimir Reshetnikov's ProveIt programme,
10 October 2026. The package is additive; it did not change the repository
or the persistent Library.

## Reading and integration

`article.pdf` is the complete 25-page article, with 16 named statements and
11 proposed further research questions. `article.tex`, `sections/`, and
`references.tex` are the editable modular sources.
`reciprocal_lerch_convolutions.tex` is the generated, self-contained single-file
source. It can be compiled without the modular source tree.

`integration/README.md` gives suggested placement and status wording.
`integration/manuscript_insert.tex` is a short, independently compilable
insertion when used with `integration/insert_preview.tex`.
`integration/theorem_index.json` lists the principal statements and their scope.
`SOURCE_AUDIT.md` records the inspected material and the limits of the audit.

## Main proved results

For F(a,s;y) = y Phi(-y,s,a), Re(a)>0, the ordinary reciprocal integral is
E(a,s+t), where E(a,v)=v zeta(v+1,a) and E(a,0)=1. All spectral orders may
be complex. At a=1, F=-Li_s(-y).

An r-fold convolution depends on the orders only through their sum. Explicit
central-factorial polynomials give finite Lerch expressions, and finite
Hurwitz/alternating-Hurwitz expressions at zero logarithmic fugacity.
Every mixed polynomial logarithmic weight is handled by a finite exact
recurrence. Its two-factor specialization has a closed pole-free formula.

Order derivatives yield ordinary convergent Stieltjes products. Additional
results cover Gamma-weighted integrals, polylogarithmic remainders, Gaussian
odd parts, unequal-shift reductions, rational-polynomial-in-pi-squared lattice
identities, harmonic coefficient formulas, and anchored primitives.

The elementary transform and convolution mechanisms are classical. No global
priority claim is made. The canonical S4 proof is unchanged; the canonical
S6 and revised S8 conjectures are not proved or refuted by this work.

## Reproduction

The executed environment used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.
Install the two Python dependencies using `requirements.txt`. A standard
LaTeX installation with the packages named in the preamble is also needed.

```sh
python code/verify.py --exact-only
python code/verify.py
make pdf
python code/make_standalone.py
```

The completed run contains **336 exact symbolic assertions, 91 numerical
diagnostics at 55 working decimal digits, and 3 negative controls**.
See `data/verification.json` for every check and threshold. The numerical
checks are floating-point diagnostics, not rigorous enclosures or proofs.
The analytic proofs are in the article. No proof-assistant verification is
claimed. The harmonic-remainder quadrature explicitly uses a finite cutoff.

The exact program generates `data/central_polynomials.json` and
`data/moment_polynomials.json`. To generate further symbolic identities:

```sh
python code/generate_identities.py --depth 2 --weights 2,0 --center --expand-central
python code/generate_identities.py --depth 3 --weights 1,1,0 --center --tex
```

In generator output, `C(r,a,v,mu)` is the convolution family,
`E(a,v)` is its entire depth-two central specialization, and `Eta(a,v)` is
the alternating Hurwitz function. These are symbolic function names.
The order variables are `s1,...,sr`; their sum is expanded explicitly.

## Important normalizations

E(a,0)=1, not zero. The first logarithmic moment has the factor (s-t)/2.
A depth-four resonance at total order -2 contains the nonzero term 1/3.
Keep branch-cancelled Lerch sums and polylogarithmic remainders combined.
For Re(a)<=1/2, the symmetric Gamma contour is not the stated contour;
use the admissible nonsymmetric line described in the article.

A finite positive-integer-order partial fraction formula cannot simply be
differentiated as an identity in independent complex orders. Use the full
analytic multiplier in that case.

## Document validation

The modular article, standalone source in a clean directory, and two-page
insertion preview were compiled. The modular and standalone PDFs have identical
extracted text. Rendered-page review found no clipping or missing mathematical
glyphs. Build and layout scope is recorded in `data/artifact_qa.json`.
