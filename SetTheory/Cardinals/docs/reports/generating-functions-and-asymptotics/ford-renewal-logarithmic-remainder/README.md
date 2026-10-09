# Sharp logarithmic remainders for Ford's renewal recurrence

Research package prepared for Vladimir Reshetnikov, 8 October 2026.

Read `article.pdf` for the complete manuscript. `article.tex`, `sections/`,
the included vector figures, and the generated table fragments form its
complete source. No network access is needed to compile it.

## Main result

For

\[
a_j=(j+1)\log(j+1)-j\log j-1,\qquad
g_0=1,\qquad g_n=\sum_{j=1}^n a_jg_{n-j},
\]

let \(\rho\in(0,1)\) solve \(\sum a_j\rho^j=1\), and let
\(\gamma=(\sum ja_j\rho^j)^{-1}\). The article proves

\[
g_n=\gamma\rho^{-n}-\frac1{n^2\log^2n}
\left(1+\frac2{\log n}-\frac{\pi^2}{2\log^2n}
-\frac{2\pi^2+8\zeta(3)}{\log^3n}+O(\log^{-4}n)\right).
\]

It gives every fixed logarithmic order, every fixed algebraic order with
the logarithmic coefficient functions retained as convergent integrals,
and an exact positive measure representing the remainder for **n >= 1**.
That indexing excludes g0, whose pole-subtracted error has the opposite sign.

Further proved results include:

- strict complete monotonicity and positive definite shifted Hankel matrices;
- explicit bounds with constants 1/200 and 10 from n = 4096 onward;
- two exact sum rules and their tail asymptotics;
- a positive normalized product constant and finite, computable tail bounds;
- a sharp correction to the product-based continuous totient counting scale;
- inversion of the relative renewal-error law;
- a theorem for a broader class of moment-increment renewal recurrences;
- a shifted-coefficient family with an explicitly vanishing first correction.

## Mathematical status and priority

These are conventional mathematical proofs, independently checked during
preparation. They have not been externally refereed or formalized in Lean.

Ford's revised *The distribution of totients*, Lemma 3.7, proves a bounded
absolute recurrence error. Its following remark already records negativity,
monotonicity, and an exact sum. Those facts and the general spectral method
are not claimed as newly invented here. The sharpened asymptotic law and its
extensions are proved independently in the manuscript.

The Ford-Lau 2000 Monthly solution was identified bibliographically but its
full text could not be inspected. The targeted priority search therefore
does not establish worldwide first-publication priority. See
`CLAIM_STATUS.md` and the article's opening section.

The paper does **not** prove a new asymptotic formula or a new error bound for
the full number of distinct totients. Its statements about that application
are restricted to the explicitly defined continuous product scale.

## Rebuild the PDF

With pdfLaTeX, latexmk, and standard AMS/LaTeX packages installed:

```sh
make pdf
```

Without `make`, run the following command repeatedly until cross-references
settle (normally three runs), then use `build/article.pdf`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex
```

Create `build/` first if it does not exist. Standard packages include
`lmodern`, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `microtype`,
`booktabs`, `graphicx`, `xcolor`, `enumitem`, `fancyhdr`, `hyperref`, and `xurl`.

## Reproduce the calculations

```sh
python -m pip install -r requirements.txt
python code/verify_recurrence.py --nmax 1000 --out rerun/data
python code/verify_symbolic.py --out rerun/symbolic_checks.json
python code/make_figures.py --input rerun/data --out rerun
```

These commands preserve the originally recorded data and figures. On systems
whose Python command is `python3` or `py`, use that command instead.
`make verify` runs the first two programs using `python3` by default.

The numerical layer compares a high-precision recurrence, a positive
finite spectral discretization, and a scaled endpoint integral. It includes
computations through n = 1000 and endpoint-integral diagnostics through
n = 10^100. Numerical agreement is not an interval certificate.

The symbolic checker verifies exact finite algebra. Those checks complement
the infinite-dimensional and asymptotic proofs; they do not replace them.
See `code/README.md`, `data/diagnostics.json`, and `VALIDATION.json` for scope
and the actual preparation parameters.

## Package map

| Path | Purpose |
| --- | --- |
| `article.pdf` | Complete research article. |
| `article.tex`, `sections/` | Full editable LaTeX source. |
| `code/verify_recurrence.py` | High-precision recurrence and independent numerical representations. |
| `code/verify_symbolic.py` | Exact coefficient and finite algebra checks. |
| `code/make_figures.py` | Rebuild figures and table fragments from data. |
| `data/` | Recorded CSV/JSON calculations and LaTeX table fragments. |
| `figures/` | Vector PDF figures and PNG previews. |
| `CLAIM_STATUS.md` | Mathematical and novelty boundaries. |
| `provenance.json` | Pinned repository and primary-source references. |
| `VALIDATION.json` | Actual build, numerical, and visual inspection record. |
| `manifest.json` | SHA-256 and byte sizes of the packaged files, excluding the manifest itself. |

A proposed repository destination is
`Analysis/RenewalTheory/Research/Ford_Renewal_Logarithmic_Remainder/`.
No repository content was changed or published while preparing this package.
