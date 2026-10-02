# Five OEIS asymptotic conjectures for distinct-partition norms

Research report prepared for Vladimir Reshetnikov, October 1, 2026.

## Read the report

`article.pdf` is the compiled article; `article.tex` is its self-contained LaTeX
source (bibliography included, no BibTeX step). The document proves the fixed
positive-tilt asymptotic formulas currently labelled conjectural in A022629,
A092484, A265840, A265841, and A265842, and develops the following refinements:

- All fixed orders of the inverse-logarithmic expansion of log a_alpha(n), with
  seven explicit correction polynomials and an algorithm for further orders.
- Exact-saddle coefficient asymptotics and all fixed Edgeworth orders.
- Lambert-W inversion for the first index reaching a specified large value.
- Logistic occupation boundaries, a Gumbel law for the largest part, and an
  explicit asymptotic for fixed Fourier-resonance moduli.

The report is not a peer-reviewed publication or a Lean-checked proof. It supplies
English proofs and distinguishes them from formal symbolic checks and numerical
diagnostics. Targeted literature review does not certify global priority. In
particular, the relationship with the shrinking-tilt analysis in a March 2026
thesis by D. K. Gikunda is explicitly discussed.

## Important finite-size caveat

The central saddle approximation is extremely good for alpha=1 at n=5000 after
two corrections, but NOT for the higher moments at the same n. For alpha=5 the
exact/central ratio is about 1.58. The report presents this failure openly and
explains the relevant Fourier-resonance scale. A fixed truncation of the
logarithmic expansion also need not improve monotonically at a fixed n.

The complete phase-sensitive multi-saddle coefficient transseries is a proposed
follow-up project, not a claimed result of this package.

## Reproduce

Python 3.10 or later, with the dependencies in `requirements.txt`, is sufficient.
No network access is needed after installing those dependencies.

```sh
python -m pip install -r requirements.txt
python verify.py --max-n 5000 --dps 50
python derive_series.py
python derive_inverse.py
python check_continuum.py
python check_resonances.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

A further LaTeX pass may be needed after changing the contents or page layout.
The bundled PDF has resolved references and was rendered and visually checked.
Standard LaTeX packages include lmodern, amsmath, amsthm, mathtools, mathrsfs,
geometry, microtype, booktabs, hyperref, bookmark, fancyhdr, enumitem, and listings.
No font files are bundled.

`verify.py` has optional `--max-n`, `--dps`, and `--alpha` arguments. For a quick
run, use `--max-n 300 --alpha 1`. Full exact calculations use O(max_n^2) integer
operations per alpha and memory O(max_n); very large n is intentionally not a
default. Running a subset writes a subset to `data/diagnostics.csv`; run all five
alphas to regenerate the full table used by the other diagnostics.

## Verification status

Executed in the delivered build:

* Independently generated all five lists through n=5000 using exact Python
  integers; compared the first sixteen terms against consulted OEIS entries.
* Checked an independent logarithmic-derivative recurrence through n=150 for
  each alpha, including exact divisibility at each step.
* Checked strict monotonicity at all n=1,...,4999 in each computed list.
* Evaluated numerical saddles/cumulants at n=100, 1000, 5000 for each alpha, with
  50 requested decimal digits plus guard digits and exponentially bounded tails.
* Generated and checked the seven displayed logarithmic polynomials and the
  inverse coefficients by exact SymPy algebra.
* Independently evaluated continuum integrals at s=12,24,48,96 for alpha=1,3.
* Evaluated the first-resonance modulus at n=5000 for every alpha.

Floating-point tail bounds and Newton solves are not outward-rounded interval
calculations; their outputs are diagnostics, not rigorous numerical certificates.
The asymptotic proofs are in the article and do not depend on trusting a fit.

## Data

`data/A*_computed.txt`: complete independently computed integer lists.
`data/diagnostics.csv`: exact-coefficient versus numerical saddle comparisons.
`data/diagnostics_alpha*.csv`: the corresponding per-column tables.
`data/continuum_diagnostics.csv`: independent integral checks of the P8 limit.
`data/resonance_diagnostics.csv`: exact numerical product moduli at theta=2*pi/M.
`data/formal_coefficients.txt`, `data/inverse_coefficients.txt`: symbolic results.
`data/*run*.txt`: execution transcripts.

## Repository integration

The comparison is with ProveIt snapshot
`1f1981f682b2878bde51a6ad40c22777f362fc05`, especially
`Analysis/Transseries/README.md`. No repository content was modified, no OEIS
entry was edited or submitted, and no Lean verification is implied.

Mathematical notation and source attribution are in the article. All code in
this package was written for this report. Computed lists are newly generated;
OEIS entry identifiers and the attribution of the original conjectures are
preserved in the bibliography.
