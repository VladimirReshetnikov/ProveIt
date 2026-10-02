# Theta Asymptotics for High-Power Ballot Sums

Research article and reproducibility package, 1 October 2026.

The article studies OEIS **A357825**, **A357871**, and the growing-power array
**A357824**, using the ballot triangle A008315. It was prepared as a proposed
addition to the ProveIt research corpus. The repository was inspected but
not modified.

## Main results

For the ordered-tuple count `a_n`, the article derives a phase-uniform
all-orders expansion whose leading factor is

    a_n / A_n = exp(-5/6) Theta(alpha_n) + O(n^(-1/2)),
    A_n = 2^(n^2 + 3n/2) / (pi^(n/2) exp(n/2) n^n),
    alpha_n = (sqrt(n+1) - ((n+1) mod 2))/2,
    Theta(alpha) = sum_{j in Z} exp(-4(j-alpha)^2).

The subsequent coefficient functions are explicit polynomial-Gaussian sums,
and hence finite linear combinations of theta derivatives. The exact
normalized liminf and limsup are approximately 0.31986675953099572613 and
0.45051819401966197435. The report also proves a limiting phase law,
eventual strict log-convexity, and non-P-recursiveness.

For the multiset count `b_n`, the first exponentially small relative sector is

    n! b_n / a_n = 1 + sqrt(pi*e)/(4*sqrt(2)) n^3 2^(-n) (1 + O(1/n)).

An exact rising-factorial identity gives every fixed exponential sector,
each with its own all-orders algebraic expansion.

The growing-power array has a continuous-Gaussian to lattice-theta
transition when the power is comparable to the row index. An exact
adjacent-entry ratio yields a uniform two-endpoint approximation for
**all** supercritical powers, without an upper restriction on the power.
Near square-index ties there is a second, logistic transition at powers
of order n^(3/2). Parity-sensitive inverse formulas are also developed.

## Contents

- `article.pdf`: the compiled research article.
- `article.tex`: complete LaTeX source, with bibliography embedded.
- `figures/`: figures used by the TeX source, as PDF and PNG.
- `code/verify.py`: independent exact checks, symbolic coefficient generation,
  high-precision full-sum evaluations, inverse tests, and plot generation.
- `data/`: CSV numerical tables, symbolic coefficients, constants,
  software versions, and the actual verification-status JSON.
- `source_audit.md`: provenance, search scope, and claim boundaries.
- `requirements.txt`: versions of the Python packages used for this run.
- `build.sh`: checks and builds the article with three LaTeX passes.
- `SHA256SUMS`: hashes of the distributed files, excluding this hash list itself.

## Reproduction

Use Python 3.10 or newer and a LaTeX installation with pdfLaTeX, newpx,
amsmath/amsthm, mathtools, microtype, geometry, graphicx, booktabs, enumitem,
fancyhdr, hyperref, and bookmark. The tested Python version is recorded in
`data/software_versions.json`.

From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py --all
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Dependency installation may need network access. The verification program
itself does not use the network. Its OEIS comparison values are embedded
with source attribution in the article.

On a POSIX shell, after dependency installation:

```sh
./build.sh
```

`build.sh` writes temporary LaTeX files to `_build/` and copies the final PDF
to `article.pdf`. Set the `PYTHON` environment variable to choose a different
Python executable. On Windows, the four explicit verification/LaTeX commands
above can be run directly in PowerShell or a terminal.

Running `python code/verify.py` without flags performs exact and symbolic
checks only. `--all` also generates tables, inverse calculations, and plots.
The symbolic generator can produce additional specified orders; the supplied
numerical approximation routine supports orders zero through six.

## Verification actually performed

All assertions passed:

- 2,601 ballot entries through n=100: independent path dynamic programming,
  reflection formula, and shifted-binomial formula.
- First 15 terms of each target sequence against OEIS.
- Exact rising-factorial bridge through n=25.
- Fixed-power column identities for powers one and two through n=100.
- Exact adjacent-entry ratios through n=100 and square-index tied maxima
  for s=2,...,20.
- Symbolic coefficients through order six, including parity checks.

The main numerical table uses all endpoints and exact integer bases at
75 decimal digits, for n=25,50,100,200,400,800,1200. The plot routine uses
localized log-Gamma sums at 45 digits; it is not the full-sum reference
calculation. Inverse and near-square transition tables use high-precision
full sums. None of these numerical evaluations is an interval certificate.

## Scope and caution

The OEIS already records the root-scale growth and the failure of a
constant normalized limit. Those observations are attributed rather than
claimed as discoveries. The report supplies self-contained proofs and
substantial refinements. A limited literature search did not establish
publication priority; no priority claim is certified.

There is **no Lean formalization in this archive**, and the report has not
been independently refereed. Exact checks and high-precision experiments
support the derivations but do not replace the analytic proofs.

The separate conjecture `a_(2p-1) = 1 mod p^3` recorded in A357825 is **not
resolved** here. No global all-index log-convexity claim, convergent infinite
asymptotic series, optimal-truncation theorem, or unrestricted exact inverse
rounding theorem is made.
