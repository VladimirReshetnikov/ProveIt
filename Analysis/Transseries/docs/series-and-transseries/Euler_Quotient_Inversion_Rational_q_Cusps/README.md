# Complex Transseries Reversion at q-Cusps

**Convergent normal forms, infinitely flat limits, logarithmic–Puiseux inverses,
and recovery from cusp data**

Research article prepared for Vladimir Reshetnikov, 4 October 2026.

## Read the article

`article.pdf` is the 27-page article. `article.tex` is the complete, editable,
self-contained LaTeX source, with its bibliography embedded. It does not require
files from ProveIt, external figures, or custom font files.

The principal results are:

- A convergent parameter-lift theorem for prepared complex exponential
  transseries, with coefficient extraction, action transport, and inverse
  residual bounds (Theorem 3.1).
- A complete local logarithmic–Puiseux inverse atlas for infinitely flat limits,
  with coherent branch indices and an explicit remainder bound (Theorem 5.1
  and Corollary 5.2).
- Exact Euler-quotient preparation at every rational cusp and a three-invariant
  classification into four inverse regimes (Theorems 6.1 and 7.1).
- Four-factor minimality at q=1 and an exact intrinsic correction-ramification
  criterion. Four factors realize every positive finite correction degree
  (Theorems 7.2 and 7.3).
- Recovery of every Euler-quotient exponent from leading divisor-cusp actions
  by a double Möbius inversion (Theorem 9.1).

The article also gives two explicit product inverses, an all-orders
fixed-parameter q-Pochhammer inverse, finite Gaussian-multinomial critical
inverses, sectorial jump transport, and fourteen further research topics.

## Scope and research status

The article gives conventional proofs of its stated local results. It
attributes the classical modular transformation, Lagrange inversion, and
resurgent closure machinery. Worldwide novelty and independent validation
of the proposed combined results have not been established. It does not
claim a universal theorem for arbitrary transseries supports or unspecified
summation operators. No Lean formalization is included.

The repository comparison is based on the targeted documentation listed in
`SOURCES.md`, not an exhaustive audit of the canonical volume or all incoming
articles. No repository files were changed.

## Verification

Run with Python 3.10 or newer:

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

The program needs no network after installing mpmath. It can be run from any
working directory and overwrites its local `data/verification.json` using
LF line endings. `data/run_summary.txt` is the recorded console output.

The included run passed **619 exact assertions**, **15 complex-cusp modular
identity tests**, the four inverse reconstructions, and the two ramified
branch checks. Numerical calculations used 115 decimal digits. The code
uses ordinary arbitrary-precision arithmetic, not outward-rounded complex
intervals. It is a diagnostic test suite, not a machine proof or interval
certificate. The formal proofs are in the article.

The complex inverse test determines the logarithmic deck from the known
reference solution. This checks the formula on the correct sheet; it is not
an automatic sheet-selection algorithm for an unknown inverse. An actual
application must specify its branch or continuation path.

Exact rational outputs are platform-independent. Last digits of floating
checks can vary by environment. Do not run Python with assertions disabled.

## Build the PDF

A standard TeX Live installation with the packages listed in `article.tex`
is sufficient:

```sh
sh build.sh
```

Equivalently, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
three times from this directory. No BibTeX step is needed.

The delivered PDF was compiled with stable references and no LaTeX warnings,
undefined references, overfull boxes, or underfull boxes. Its final pages were
rendered for layout inspection. See `BUILD_REPORT.json` for the recorded
checks. Rebuilding may change PDF metadata and checksums.

## Package contents

- `article.tex`, `article.pdf`: source and compiled article.
- `code/verify.py`: exact and numerical verification program.
- `data/verification.json`, `data/run_summary.txt`: recorded results.
- `requirements.txt`, `build.sh`: reproduction instructions.
- `SOURCES.md`, `PROVENANCE.json`: source boundary and repository snapshot.
- `BUILD_REPORT.json`, `SHA256SUMS.txt`: build validation and integrity ledger.

The archive does not contain TeX auxiliary files, private working notes,
rendered inspection images, or font files.
