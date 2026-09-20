# An explicit formula for lucky parking spots

Research manuscript prepared for Vladimir Reshetnikov, 19 September 2026.

## Result

For integers 1 <= j <= n, with x = n-j+1, the article proves

    C(n,j) = ((j+1)*(n+1)^(n-1)
              - sum(binomial(n,k)*j^k*x^(n-1-k), k=0..j-2)) / (2*j).

C(n,j) counts ordinary parking functions in which **spot** j is lucky.
The sum is empty for j=1. This gives the polynomial asserted in Conjecture 13
of Butler–Hadaway–Lenius–Martens–Moats (JIS 29, 2026, Article 26.1.1):

    f_j(n) = sum(binomial(n,k)*j^k*(n-j+1)^(j-2-k), k=0..j-2)/(2*j).

The article includes a complete conventional proof, an exact reflection law,
all fixed right-edge columns, a closed form for OEIS A374533, Poisson edge
limits, uniform bulk convergence, polynomial reciprocity, and asymptotic
expansions. The target remains labeled a conjecture in the consulted primary
source. A targeted search did not find a published resolution; this does not
establish exhaustive priority. The proof has not been peer-reviewed or
verified by a proof assistant.

## Files

- `article.pdf`, `article.tex`: full article and editable source.
- `code/verify.py`: exact verifier/data generator, Python standard library only.
- `code/make_figures.py`: optional matplotlib figure generator.
- `data/triangle.csv`: all 5,050 entries with 1 <= j <= n <= 100, and P_n.
- `data/f_polynomials.json`: ascending rational coefficients of f_j, 2 <= j <= 30.
- `data/boundary_limits.csv`: exact rational factors and 50-decimal-place limits.
- `data/a374533_extension.txt`: local next-to-last-column extension to n=100.
- `data/verification.json`, `data/verification_console.txt`: actual check results.
- `figures/`: vector PDF and PNG versions of both figures.
- `source_audit.md`: provenance, consulted versions, and indexing cautions.
- `Build.ps1`, `Makefile`: optional build helpers.

## Reproduce the exact checks

From this directory, on Windows, Linux, or macOS:

```text
python code/verify.py
```

Python 3.9 or later is sufficient. No network access or third-party packages
are used. The default run verifies every column through n=100 against the
last-arrival recurrence, simulates all preference lists through n=7, runs a
direct occupancy-state dynamic program through n=12, enumerates outcome
permutations through n=8, and checks exact polynomial identities through j=30.
Finite checks support but do not replace the article's mathematical proofs.

For a larger recurrence/formula test:

```text
python code/verify.py --max-n 200 --poly-j 50 --output-dir data-large
```

The `--brute-n` bound is deliberately small: its work grows as n^n.
The `--outcome-n` bound grows factorially and the occupancy DP exponentially.

## Rebuild the PDF

The PDF was built with pdfLaTeX. A TeX installation needs the packages named
in `article.tex`, including `newpxtext`, `newpxmath`, `amsmath`, `amsthm`,
`mathtools`, `microtype`, `booktabs`, `titlesec`, `tcolorbox`, `hyperref`,
`listings`, and `needspace`.

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The provided vector figures suffice for recompilation. Regenerating them is
optional and requires matplotlib:

```text
python code/make_figures.py
```

`./Build.ps1` performs the verification and the two LaTeX passes in PowerShell;
`make` does the same where GNU Make is available.

## Counting conventions

Cars arrive in label order and move only to the right from their preferences.
A spot is lucky if its occupant preferred that spot. This is not the same as
asking whether a car of a specified arrival label is lucky. Data rows use
explicit `(n,j)` coordinates rather than a potentially ambiguous flattened
triangle. A374533 starts at n=2. The generated extension is not an OEIS
submission; no external account or encyclopedia entry has been modified.
