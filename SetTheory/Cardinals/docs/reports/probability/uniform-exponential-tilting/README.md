# Uniform exponential-tilting guarantees

This research package contains a complete article, proofs, certified numerical code, and exact rational checks.

## Results

1. A prescribed coefficient of a product of positive linear factors can be approximated with a uniform relative-error guarantee using O(log(1/epsilon)) Fourier evaluations after a coarse exponential tilt. Binary multiplicities are supported without expanding the product. Representative conditional inclusion marginals have simultaneous additive-error guarantees.
2. A tilted probabilistic divide-and-conquer sampler for arbitrary two-row contingency tables needs fewer than 5 sqrt(n) expected proposals at ideal centering, or 5e sqrt(n) with a constructible rational tilt. The article proves a polynomial-bit realization and a sharper instance-dependent bound.

Tilting, Fourier sparsity, and probabilistic divide-and-conquer are established methods. The article identifies the precise quantitative strengthenings, cites the closest primary sources, and limits its priority claims to the literature surveyed.

## Contents

- `paper.pdf`: complete typeset article.
- `paper.tex`: complete LaTeX source, including its bibliography.
- `code/certified_coefficients.py`: actual Arb/Acb interval implementation for probabilities and positive-factor coefficients.
- `code/test_certified_coefficients.py`: independent exact-rational and log-gamma checks.
- `code/sampling_checks.py`: exact finite-capacity reference sampler and exhaustive checks.
- `code/reproduce.py`: regenerates tests, example records, article tables, and the figure.
- `results/`: machine-readable certificates, CSV data, test results, and generated LaTeX tables.
- `figures/`: standalone PDF and PNG versions of the frequency-count figure.
- `sources.json`: primary-source provenance and literature-review scope.
- `requirements.txt`, `Makefile`: reproduction and compilation instructions.

## Reproduce

Python 3.10 or later is required. The tested environment used Python 3.12 and python-flint 0.9.0.

```bash
python -m pip install -r requirements.txt
python code/reproduce.py
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

A normal TeX Live installation providing Palatino, AMS packages, microtype, hyperref, titlesec, and booktabs suffices. No bibliography tool or shell escape is needed. `make all` runs reproduction and compilation.

To run only the exact sampling checks:

```bash
python code/sampling_checks.py
```

To run only the coefficient tests:

```bash
python -m unittest discover -s code -p 'test_*.py' -v
```

## Certified coefficient API

```python
from certified_coefficients import certify_probability, certify_coefficient

# A trillion Bernoulli trials, described by one group.
answer = certify_probability(
    ["1/1000000"],
    10**9,
    epsilon="1e-12",
    multiplicities=[10**12],
    marginals=True,
)

# [z^80] (2+3z)^50 (5/7+11z/13)^75.
coefficient = certify_coefficient(
    [("2", "3"), ("5/7", "11/13")],
    80,
    multiplicities=[50, 75],
    epsilon="1e-12",
)
```

Run this with `code` on Python's import path, or place the script in that directory. A command-line JSON interface is also supplied:

```bash
python code/certified_coefficients.py --input examples/rare_binomial.json --output answer.json
```

Inputs must be exact integers, `Fraction` objects, or rational/decimal strings. Binary floats are rejected so that the certified input is unambiguous. The output contains exact dyadic endpoints of the form `mantissa * 2**exponent`; the accompanying formatted ball string is for readability. Logarithmic output remains usable for probabilities far below hardware underflow. The exact JSON endpoints are authoritative; CSV decimal midpoints, decimal width displays, and formatted Arb strings are readable diagnostics rather than outward-rounded certificates. The code returns only after its interval-width criteria are verified, or raises `CertificationError` if its precision/iteration limit is reached.

For grouped input, each returned marginal is for one representative Bernoulli trial. Multiplying by the group's multiplicity also multiplies its additive error. Relative coefficient accuracy and additive marginal accuracy are different guarantees.

## Implementation scope

The coefficient implementation uses ball arithmetic for its actual evaluations, plus the proved analytic alias and truncation bounds. The implemented tilt search is separately counted and conservative; the sharper bisection--Newton operation bound in the article is a mathematical algorithm theorem. The `tilt_evaluations` statistic counts completed searches/checks and omits partial searches interrupted for more precision; it is not a total-work counter.

The table-sampling program is a readable exact reference for moderate capacities. It forms finite rational weight arrays and therefore does **not** realize the article's binary-size random-bit implementation. The article supplies the constructive proof and specifies lazy inverse-CDF primitives for that implementation. The test program never labels floating diagnostic displays as exact comparisons.

The plots show operation counts and accuracy dependence. Timings in the records are observations for the supplied implementation, not a comparison with an optimized production FFT package. The proofs have been independently checked within this research session; no external peer review or Lean formalization is asserted.
