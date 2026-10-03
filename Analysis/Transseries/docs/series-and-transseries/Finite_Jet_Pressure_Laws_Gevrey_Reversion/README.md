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

(Editorial, 2026-09-30: the critical-window theorem also answers the predecessor's question "Uniform transitions at the lower thresholds", which the article does not claim; the predecessor now carries reciprocal notes. See the amendments below.)

## Scope and priority

The proofs are conventional mathematics, not Lean verification or peer review. The contribution is measured against the identified repository question. Global publication priority has not been established. In particular, superexponential tree condensation, independent Poisson approximation, and leading centering corrections have published precedents in Janson, Jonsson, and Stefansson (2011); the article credits these and distinguishes its explicit all-order formulas.

The theorem assumes an eventually exact shifted-factorial tail and strictly positive weights. It is not a result for arbitrary oscillatory weights or arbitrary signed inverse coefficients. It is uniform on suitable compact positive-order parameter sets, not as `s` tends to zero. A complete multiplicative equivalent means relative error tending to zero, not an effective finite-degree error estimate.

## Package contents

- `article.tex`: standalone LaTeX source with embedded bibliography and tables.
- `article.pdf`: 24-page compiled A4 article (23 as delivered; the editorial notes of 2026-09-30 add one).
- `code/verify.py`: standard-library exact rational/integer checks.
- `code/diagnostics.py`: optional non-certified log-scaled numerical diagnostics.
- `data/verification.json`: results of 1,066 exact finite scalar checks.
- `data/diagnostics.csv`: 45 numerical cases, up to degree 10,000.
- `data/numeric_validation.json`: fifteen degree-70 cross-checks at 80 decimal digits.
- `data/numerical_table.tex`: generated copy of the table embedded in the manuscript.
- `data/build_validation.json`: actual PDF build, geometry, and visual review record (its page count and digests were recomputed for the editorial rebuild; see below).
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

Both programs now write to `data/rerun/` by default, so the recorded files stay unchanged; only an explicit `--output` into `data/` overwrites them (as delivered, the defaults wrote to the recorded data paths):

```sh
python code/verify.py --output data/verification.json
python code/diagnostics.py --max-n 10000 --output data
```

In this repository, on Windows, use `py code/verify.py` and `uv run --no-project --with numpy==2.3.5 --with scipy==1.17.0 --with mpmath==1.3.0 python code/diagnostics.py`; bare `python` (and the `Makefile`'s `python3`) may not resolve. The diagnostics use double precision, not an extended `long double`, so they run on Windows.

Build the article with a standard TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or use `make check`, `make diagnostics`, and `make pdf`. The TeX source does not depend on the generated data files. PDF metadata, including compilation time, may change on rebuilding; the recorded PDF digest then no longer describes that rebuild.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batch 65 of `docs/incoming/` (see `docs/incoming/README.md`); every change to the source is marked `% ed. (2026-09-30)`, every change to a program `ed. (2026-09-30)`. The title page and PDF metadata name ChatGPT and the addressee; they are kept as delivered, as in the subexponential-cost article beside this package.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt, 2026-09-30)" is defined in the preamble (the theorem counter is unchanged). Two notes:
  - end of Section 1.1: four neighbouring packages are not cited. `../Exact_Weighted_Type_Beyond_Log_Convexity/` asks for the optimal subexponential overhead of reversion for a specified weight profile (its question "Optimal subexponential overhead", whose editorial note records the factorial answer of the predecessor); for eventually shifted-factorial weights with an arbitrary positive head, not necessarily log-convex, Theorem `thm:main` determines the extremal cost in this article's normalization, while the general question stays open. `../Finite_Core_Universality_Exponential_Feedback/`, `../Microscopic_Condensation_Exponential_Feedback/` and `../Poisson_Layers_Finite_Core_Boundary/` use the same Poisson small-part mechanism for a different kernel (the first also cites Janson, Jonsson and Stefansson);
  - after Theorem `thm:windows` and its remark: it answers the predecessor's question "Uniform transitions at the lower thresholds", which the article does not claim; the remainder is `o(1)` uniformly for bounded `t`, not effective.

  Four bibliography entries (`ed:exacttype`, `ed:finitecore`, `ed:microcond`, `ed:poissonlayers`) are added for those packages, so the later references are renumbered in print. No label was renamed or removed.
- `article.pdf`: rebuilt from the amended source by the three `pdflatex` passes above (MiKTeX pdfTeX 1.40.29): 24 pages (23 as delivered), no error, overfull box, undefined reference, multiply defined label, or duplicate destination, and the one underfull box of the delivered build; every font is embedded and none is Type 3. The pages carrying the notes and the bibliography were rendered and inspected.
- `data/build_validation.json`: `pdf_pages`, `source_sha256` and `pdf_sha256` recomputed for the filed files, and an `editorial_rebuild` field says so; its other fields describe the delivered build.
- `code/verify.py`: the default `--output` is `data/rerun/verification.json`, and the JSON is written with LF line endings on every platform (as delivered, the platform's, so CRLF on Windows).
- `code/diagnostics.py`: the default `--output` is `data/rerun/`; the JSON and TeX outputs are written with LF line endings on every platform (the CSV writer already was).
- Reruns on a copy (2026-09-30, the commands above, Python 3.14.4 for `verify.py`): `data/verification.json` and `data/numerical_table.tex` were reproduced byte for byte; `data/diagnostics.csv` differs in 28 cells in the last digits (at most 6.7e-13 relative) and `data/numeric_validation.json` in one cross-check value (7.1e-15 against 2.1e-14 absolute log difference), floating-point noise of the platform.
- `README.md`: the pointer under "Research result", the page count, the build-record description, the output location and Windows commands, and this section.
- Recorded, not changed: the unused bibliography entry `repo`; the letters `A` (ball radius and weight polynomial), `B`, `P` and `S_n` have several meanings here, and `a_j = C w_j` are weights, not the predecessor's forward coefficients.
