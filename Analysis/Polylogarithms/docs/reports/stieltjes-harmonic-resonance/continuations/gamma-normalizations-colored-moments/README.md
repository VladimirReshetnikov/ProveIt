# Gamma Determinants and Colored Stieltjes Moments

Research continuation prepared for Vladimir Reshetnikov's ProveIt programme,
12 October 2026.

## Read the article

- `Gamma_Determinants_and_Colored_Stieltjes_Moments.pdf` — complete 30-page article.
- `Gamma_Determinants_and_Colored_Stieltjes_Moments.tex` — complete,
  self-contained TeX source with all article inputs expanded.
- `article.tex`, `preamble.tex`, `sections/`, `references.tex` — modular sources
  intended for selective integration.

## Main mathematical results

The article evaluates all incoming Gamma-basis normalization constants,
proves exact Gaussian moment matching for a normalized trigamma statistic
through degree `n+1`, supplies the colored balanced Lerch/Stieltjes Mellin and
integer-moment calculus, and evaluates all two-cluster Gamma spectral faces
by a finite multiple-polylogarithm dictionary. It includes exceptional beta
moments, anchored primitives, an exact color-one constant-term conversion,
and a counterexample to pointwise colored uniqueness.

A supplementary exact depth-two calculation addresses one printed
Gaussian-color example. The `S_6`, revised `S_8`, and unrestricted later
harmonic-tail determinant problems remain open.

Classical input formulas are credited. New status is claimed relative to the
specific inspected repository sources, not as a proof of worldwide historical
priority. The analytic proofs are in the article; numerical agreement is never
used as a substitute.

## Build

From the package directory:

~~~bash
python3 build.py
~~~

The build requires Python 3 and a TeX installation providing `pdflatex`,
Latin Modern, AMS-LaTeX, `geometry`, `microtype`, `mathtools`, `enumitem`,
`fancyhdr`, `hyperref`, and `bookmark`. No network access is used.

`build.py` regenerates the standalone TeX, runs three LaTeX passes, rejects
overfull boxes or unresolved references, and copies the PDF to the package
root. Auxiliary build files go in `build/`.

To regenerate only the standalone source:

~~~bash
python3 build.py --tex-only
~~~

The supplied standalone TeX can also be compiled directly three times with
`pdflatex`, without the modular sources or Python.

## Verification and provenance

Install the optional verification dependencies with:

~~~bash
python3 -m pip install -r requirements.txt
~~~

Then see `verification/README.md` for the individual commands and what they
check. The recorded evidence is in `evidence/`. Exact checks use rational
arithmetic; high-precision quadratures are explicitly labelled diagnostics.
Scripts need no repository checkout or network access.

`evidence/source_manifest.json` identifies the pinned repository revision and
hashes the source archives. `integration/INTEGRATION_NOTES.md` maps the new
results to exact predecessor locations and describes the optional editorial
patch. No repository changes were pushed.
