# First Pattern Failure in Catalan Permutations
## A proof of OEIS A273821, exact formulas, all-orders expansions, and a critical phase transition

Research report prepared for Vladimir Reshetnikov, October 1, 2026.

## Main result
For n > k >= 1,

    T(n,k) = 2^(k-1) binomial(2n-2k,n-k-1)
             - binomial(2n-k-1,n-k-1),

and T(n,n)=2^(n-1). The article proves this from the permutation definition,
thereby proving the bivariate generating function marked conjectural in
OEIS A273821 on the retrieval date. It also proves the suggested growth
constant 4 for every fixed column k>=2.

Further results include hypergeometric columns, an all-orders asymptotic
coefficient engine, a discrete limiting law, an exponentially weighted
O(1/n) probability error, a square-root crossover, two separately controlled
exponential sectors, and a full tilted phase diagram. At critical weight
2^K, K/n converges to Beta(1,1/2), with exact normalization and mean. Inverse
expansions use the real W_{-1} branch and explicitly address rounding.

## Files
- `article.pdf`: complete report.
- `article.tex`: editable source, including bibliography.
- `code/verify.py`: independent exact, symbolic, and numerical checks.
- `code/make_figures.py`: figure reproduction.
- `data/verification_summary.json` and `verification_log.txt`: executed checks.
- `data/*.csv`: high-precision numerical comparisons.
- `figures/*.pdf`: vector graphics used by LaTeX; PNG copies also supplied.
- `OEIS_update.txt`: proposed changes, not submitted.
- `sources.md`: source and novelty-search record.
- `requirements.txt`, `Makefile`: reproduction aids.

## Verification that was executed
The default verifier passed on:
- Every permutation of sizes 1 through 9 (409,113 permutations).
- Every triangle entry through row 120 (7,260 cells), using an independently
  implemented suffix-state insertion dynamic program.
- Exact row sums, cumulative counts, critical normalization and first two
  moments, polynomial factorization, first-order column recurrence, and
  the OEIS triangle recurrence.
- Symbolic generating-function equality and first three correction terms.
- 100-decimal-digit numerical evaluation for the included tables.

The computations support conventional proofs in the article. They are not
Lean kernel certificates. Numerical error tables are not rigorous interval
certificates for asymptotic remainders.

## Reproduce
Python 3.10 or later, with the listed packages, is sufficient for the code.
The supplied figure files permit compiling the article without running Python.

```sh
python -m pip install -r requirements.txt
python code/verify.py > data/verification_log.txt
python code/make_figures.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

`make verify`, `make figures`, and `make pdf` are also provided. A current
TeX installation with newtx, amsmath, amsthm, mathtools, geometry, microtype,
hyperref, bookmark, titlesec, fancyhdr, enumitem and standard graphics/table
packages is required. No font files are bundled.

The verifier allows `--brute-max` (1..10) and `--dp-max` (2..400). Increasing
these can considerably increase execution time and integer sizes. No network
access is used by the scripts.

## Scope and attribution
The source definition and conjecture are due to the OEIS entry by David
Callan. Standard Catalan and analytic-combinatorics methods are acknowledged.
A000245 and A071718 are known companion columns and their previously posted
leading asymptotics are not claimed as new.

A targeted identifier/statistic search did not locate another proof of the
posted A273821 conjecture. This is not an exhaustive certification of
priority for every theorem. The exact and asymptotic results are proved in
this report; the later research directions are clearly separated from them.

The ProveIt transseries project is methodological context and a possible
formalization destination, not a logical dependency or a claim that these
results are already formalized. No repository modification or OEIS edit
was made.
