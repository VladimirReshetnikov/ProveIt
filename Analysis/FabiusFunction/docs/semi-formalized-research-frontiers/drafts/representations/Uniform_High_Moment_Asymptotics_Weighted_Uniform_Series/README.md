# Uniform high-moment asymptotics for weighted uniform series

**Research article and reproducible support package, 7 October 2026.**

The article studies `X = sum a_j U_j`, where the independent `U_j` are uniform
on `[0,1]`, every weight is positive, and the finite or countable weights sum
to one. It proves an array-uniform all-orders saddle expansion for `E[X^n]`,
sharper fixed-geometric remainders, and an optimal-order crossover theorem
for the simpler Laplace approximation. Geometric ratio `q=1/2` gives the
Fabius distribution and concrete asymptotics for `F(2^(-n))`.

## Main results

For the unique saddle `t - mu(t) = n`, let
`A = L(t) exp(mu(t)) (n/t)^n / sqrt(1+v(t)/n)`.
For each fixed order `J`, Theorem 4.1 proves

```
M_n/A = sum_{j=0}^J C_j/n^j + O_J(mu(t)/n^(J+2)).
```

Constants are independent of the number and values of the weights. Arrays
may change with `n`. For fixed geometric `q`, Theorem 5.3 proves

```
M_n/A - 1 ~ log(n) / (12 log(1/q) n^2),
M_n/[A(1+Delta)] - 1 = O_q(n^(-3)).
```

It also identifies the next sharp remainder after the full second correction.
At the original tilt `n`, Theorem 6.3 proves the explicit bound

```
abs(M_n/L(n) - exp(-mu(n)^2/(2n))) <= 15/sqrt(n).
```

Thus `M_n ~ L(n)` holds exactly when `mu(n) = o(sqrt(n))`. A calibrated
geometric family shows that the uniform `n^(-1/2)` order is optimal.

These are mathematical proof claims supported by the article's arguments.
They have not been independently refereed or formalized. Historical priority
has not been established; no claim of a verified “breakthrough” is made.
Classical tilting, Fabius identities, and existing ProveIt comparison results
are explicitly credited rather than relabeled as new.

## Contents

- `article.tex`, `article.pdf`: manuscript, proofs, comparisons, and eight research directions.
- `code/moments.py`: product/cumulant evaluation, saddle solver, independent positive moment recurrences, exact rational routines.
- `code/coefficients.py`: exact rational coefficient generator.
- `code/test_results.py`: 119 passing symbolic, rational, and high-precision checks.
- `code/experiments.py`: reproduces the supplied tables without random sampling.
- `code/evaluate.py`: command-line asymptotic evaluation, including dyadic Fabius values.
- `data/`: coefficient expressions, validation receipt, CSV data, and generated LaTeX tables.
- `THEOREM_STATUS.md`, `INTEGRATION.md`: proof boundaries and suggested repository integration.
- `provenance/`: source references, environment, build inspection, and demo output.
- `MANIFEST.json`, `SHA256SUMS`: payload inventory and hashes.

## Reproduce

Python 3.10 or later, SymPy, mpmath, and a TeX installation with `latexmk` are
required. Install Python dependencies once, then run from the package root:

```bash
python -m pip install -r requirements.txt
python code/coefficients.py
python code/test_results.py
python code/experiments.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The checks and build require no network after dependencies are installed.
Default experiments reproduce nine fixed-ratio rows, six critical rows, and
six finite-array rows. `--extended` includes more costly quadratic-time
reference computations and is not required for the shipped receipt.

A high-index evaluation that does not compute all preceding moments:

```bash
python code/evaluate.py --n 1000000 --q 0.5 --order 1 --digits 80
```

An independent reference comparison at a moderate index:

```bash
python code/evaluate.py --n 256 --q 0.5 --order 3 --digits 80 --reference
```

Use decimal strings for the ratio to avoid importing machine-double rounding.
Outputs remain numerical approximations: an asymptotic big-O theorem is not
an explicit finite-index error certificate. The product evaluator reports
analytic tail bounds, not floating-point rounding enclosures. It guards
against an excessively long geometric head when `q` is near one.

## Trust and integration

No Lean code is claimed checked, and no incomplete Lean stubs are included.
Exact symbolic checks and exact rational checks are separate from numerical
diagnostics. See `THEOREM_STATUS.md` for the detailed ledger. Suggested
placement is `Analysis/FabiusFunction/docs/research/UniformMomentAsymptotics/`.
This package does not modify or push to either referenced repository.
