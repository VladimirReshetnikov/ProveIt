# Surreal Probability and Log-Odds

**A multiscale theory of belief, information, and infinite sampling**

A standalone research article prepared for Vladimir Reshetnikov, dated
22 September 2026. The PDF has 35 pages including its title page and contents.

## Files

- `surreal_probability.tex` — complete, standalone LaTeX source with internal bibliography.
- `surreal_probability.pdf` — compiled and visually inspected article.
- `verify.py` — exact finite checks in the ordered rational-function field Q(t).
- `verification.json` — actual successful run: 2,145 assertions, Python 3.13.5.
- `build.sh` — PDF build script; uses latexmk when available, pdflatex otherwise.
- `RESEARCH_AUDIT.md` — repository pin, research scope, sources, and evidence boundaries.
- `BUILD_VALIDATION.json` — build and PDF validation summary.

## Main content

The article develops finite probability over set-sized ordered subfields of
the surreal numbers, with canonical surreal logarithms and exponentials in
an appropriate larger workspace. It proves conditional-shadow and
leading-scale Bayesian formulas, a conditioning precision theorem, a
signed-row compression for real-act preferences, softmax bounds, finite
information inequalities, strict propriety of scores, a Gibbs variational
principle, and finite-horizon stochastic results.

Its infinite-space constructions are kept distinct: strong Hahn laws,
coefficientwise hierarchies of ordinary measures, regular finitely additive
all-subsets extensions, and internal/Loeb models. The article includes
explicit nonextension examples for independently repeated nonreal coin
biases, a positivity failure for naive uncountable-support integration,
and an infinite latent-regime model with finite posteriors that do not
recover tail conditioning in ordered-field convergence.

The last example is particularly informative: a bounded posterior
martingale is not order-Cauchy on any path, yet its ordinary standard-part
behavior is consistent with the classical real martingale theorem.

## Repository comparison

The comparison uses the following Surreal repository snapshot:

    d22a5b35d5b3040e870c3cfd6d1c8f7259e094b0

The existing report at
`docs/surreal/hahn-valued-measures-and-probability/` already develops the
strong/coefficientwise distinction. This article builds on that distinction
and does not claim that non-Archimedean probability or extended logarithmic
belief models are new. The repository was not modified.

## Build

A normal TeX Live or MiKTeX installation with the packages named in the
source is sufficient. No external figures, font files, BibTeX run, or
network access is required.

```sh
sh build.sh
python3 verify.py --output verification.json
```

The verifier needs Python 3.10 or later and uses only the standard library.
It represents t as an exact positive infinitesimal, not as a small decimal.
All polynomial coefficients and calculations are exact rational arithmetic.

The build script leaves intermediate TeX files under `_build/`. Run the
verifier on a copy to preserve the originally delivered JSON record.

## Status

This is an AI-assisted mathematical exposition with written proofs. It has
not been independently refereed or fully formalized. No new Lean code is
included, and no named open conjecture or first-in-literature result is
claimed. Finite checks do not certify the infinite theorems, canonical
surreal exponentiation, choice, compactness, saturation, or measure
extension. The article identifies each required framework and its limits.
