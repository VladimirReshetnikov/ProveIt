# Finite-Jet Pressure Laws for Gevrey Reversion and Condensation

**Complete multiplicative asymptotics, explicit critical constants, and Poisson centering**

Research article prepared for Vladimir Reshetnikov, 30 September 2026.

## Research result

The article resolves the explicitly uncompleted `0 < s < 1/2` multiplicative-asymptotic problem in ProveIt's `Sharp_Subexponential_Cost_Gevrey_Reversion` package. It gives a finite coefficient formula for every nonvanishing term of the normalized logarithm, at every fixed positive Gevrey order.

For positive weights with an eventually shifted-factorial tail,

    w_j = D_* Gamma(j + nu + 1)^s   for all sufficiently large j,

and arbitrary positive finite head, define formal series

    F_theta(z) = z (1 - theta C W(z))^(1/theta),
    W(z) = sum_{j>=1} w_j z^j,

with `F_0(z) = z exp(-C W(z))`. For `theta >= -1`, put

    R_n = [z^n] inverse(F_theta) / (C w_(n-1)).

If `J >= 1` and `(J+1)s > 1`, let

    A(t) = sum_{j=1}^J C w_j t^j,
    B(t) = t A'(t) / (1 - theta A(t)),
    Psi_a(u) = integral_0^u (1-v)^(-a) dv.

The principal theorem is

    log R_n = sum_{k=1}^J p_k n^(1-k s) + o(1),
    p_k = [t^k] Psi_(k s)(B(t)) / k.

At `theta = 1`, this is the exact coefficient-ball reversion extremum. At `theta = -1`, it gives the partition function of weighted plane rooted trees. The article also proves a finite-head universality theorem, every critical window `s = 1/r + t/log n`, and a product-Poisson law with explicitly computable centering corrections.

## Scope and priority

The proofs are conventional mathematics, not Lean verification or peer review. The contribution is measured against the identified repository question. Global publication priority has not been established. In particular, superexponential tree condensation, independent Poisson approximation, and leading centering corrections have published precedents in Janson, Jonsson, and Stefansson (2011); the article credits these and distinguishes its explicit all-order formulas.

The theorem assumes an eventually exact shifted-factorial tail and strictly positive weights. It is not a result for arbitrary oscillatory weights or arbitrary signed inverse coefficients. It is uniform on suitable compact positive-order parameter sets, not as `s` tends to zero. A complete multiplicative equivalent means relative error tending to zero, not an effective finite-degree error estimate.

## Package contents

- `article.tex`: standalone LaTeX source with embedded bibliography and tables.
- `article.pdf`: 23-page compiled A4 article.
- `code/verify.py`: standard-library exact rational/integer checks.
- `code/diagnostics.py`: optional non-certified log-scaled numerical diagnostics.
- `data/verification.json`: results of 1,066 exact finite scalar checks.
- `data/diagnostics.csv`: 45 numerical cases, up to degree 10,000.
- `data/numeric_validation.json`: fifteen degree-70 cross-checks at 80 decimal digits.
- `data/numerical_table.tex`: generated copy of the table embedded in the manuscript.
- `data/build_validation.json`: actual PDF build, geometry, and visual review record.
- `PROVENANCE.json`: repository snapshot, inspected sources, and boundaries.
- `Makefile`: convenience targets.
- `requirements-diagnostics.txt`: numerical package versions used for the recorded run.

No upstream repository files or persistent Library files were modified.

## Reproduction

Run the exact checks with Python 3.10 or later:

```sh
python code/verify.py
```

The script checks both inverse compositions through degree 18, exact grouping of Lagrange sums, two independent pressure computations through degree 7, the displayed first four coefficient polynomials, critical pure-monomial coefficients, and all 256 sign patterns of a degree-nine extremal box. These finite tests are not proofs of the asymptotic limits.

Optional numerical checks:

```sh
python -m pip install -r requirements-diagnostics.txt
python code/diagnostics.py --max-n 10000
```

The diagnostics require NumPy, SciPy, and mpmath. They use ordinary floating-point arithmetic for the large-degree table, with an independent high-precision check at degree 70; none are interval-certified. A `nan` in the CSV's saddle columns means the routine did not locate the small positive branch at that finite argument. It is printed as a dash in the article, not treated as a mathematical value. The finite-degree asymptotic residuals are deliberately reported even when large or nonmonotone.

Defaults write to the recorded data paths. To keep those files unchanged:

```sh
python code/verify.py --output data/rerun/verification.json
python code/diagnostics.py --max-n 10000 --output data/rerun
```

Build the article with a standard TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or use `make check`, `make diagnostics`, and `make pdf`. The TeX source does not depend on the generated data files. PDF metadata, including compilation time, may change on rebuilding; the recorded PDF digest then no longer describes that rebuild.
