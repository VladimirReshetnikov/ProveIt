# OEIS A126764: L-convex polyominoes and a colored-partition comparison

Research manuscript, October 1, 2026. Prepared with ChatGPT for Vladimir Reshetnikov.

## Main result

Starting from the established area generating function for fixed L-convex
polyominoes, the article supplies a conventional proof of the asymptotic
recorded as the Guttmann–Kotěšovec conjecture in OEIS A126764:

    a_n ~ (13 sqrt(2) / 768) n^(-3/2) exp(pi sqrt(13 n / 6)).

It also proves three correction terms with a relative O(n^(-7/4)) remainder,
an exact coefficientwise comparison with a colored-partition Euler product,
a finite-cut identity, an all-orders positive-real-axis expansion of the
generating function, and an asymptotic inverse for a specified interpolation.

The article's K = 13*pi^2/24 is named A in the verification scripts.
The coefficient correction constants are approximately

    -1.03410521762627474 / sqrt(n)
    -1.95847649289673621 / n
    +12.5504457791462181 / n^(3/2).

The all-orders radial expansion is NOT presented as an all-orders coefficient
expansion. A complete coefficient transseries, exponentially small sectors,
and explicit universal numerical error constants remain research questions.

## Contents

- `lconvex_asymptotics.pdf`: 19-page article, including proofs, source references,
  numerical tables, inverse asymptotics, eight research directions, and a
  claim/status ledger.
- `lconvex_asymptotics.tex`: complete standalone LaTeX source; bibliography is
  embedded, so no BibTeX run is required.
- `verify.py`: exact integer arithmetic checks using only Python's standard library.
- `verify_symbolic.py`: exact symbolic and high-precision numerical checks.
- `requirements.txt`: versions of the optional Python dependencies used here.
- `checks/coefficients.csv`: a_n, comparison coefficients p_n, defects, and second
  differences for 0 <= n <= 2000.
- `checks/verification.json` and `checks/exact_checks.txt`: exact-check results.
- `checks/symbolic_checks.txt`: symbolic identities and rational coefficients.
- `checks/symbolic_run.txt`: numerical/symbolic run output.
- `checks/numerical_table.csv` and `checks/expanded_table.csv`: numerical comparisons.

## Reproduce the checks

Run from this directory, using Python 3.10 or newer. The supplied run used
Python 3.13.5. Do not use Python's `-O` option: the checkers use assertions.

```sh
python verify.py --nmax 2000 --out checks
python -m pip install -r requirements.txt
python verify_symbolic.py
```

The first command is entirely independent of third-party packages. Run it before
the symbolic checker, which reads `checks/coefficients.csv`. Neither checker
needs a network connection or downloads any data during a run.

All included assertions passed. The exact checks include the first 37 OEIS
terms, four separately read OEIS b-file anchors, the product/slopes identity,
the positive defect decomposition, the two coefficientwise majorants, the
coefficient squeeze at every index from 3 to 2000, and the third finite-cut
identity after clearing its polynomial denominator. Symbolic checks cover
Wronskians, the denominator factorization, radial coefficients through t^8,
and the three coefficient corrections.

The numerical comparisons are diagnostics, not evidence substituted for an
infinite proof. In particular, the article does not claim an independent
external comparison of every one of the 2001 computed coefficients.

## Build the PDF

Use a LaTeX installation with pdfLaTeX and the packages named in the source,
including `newpx`, `amsmath`, `amsthm`, `mathtools`, `microtype`, `tcolorbox`,
`fancyhdr`, `geometry`, and `hyperref`.

```sh
pdflatex -interaction=nonstopmode -halt-on-error lconvex_asymptotics.tex
pdflatex -interaction=nonstopmode -halt-on-error lconvex_asymptotics.tex
```

Repeat once more if LaTeX reports changed cross-references. No auxiliary
figures, external data files, or bundled fonts are needed to build the article.
The supplied PDF was compiled and visually reviewed; its final compilation
reported no overfull boxes or unresolved references.

## Proof and priority status

The exact enumerative generating function is a cited prior result. The article
supplies the asymptotic argument, rather than assuming an asymptotic claim from
ProveIt. A targeted repository search returned no A126764 match; this is not a
claim that every repository file or previous report was exhaustively audited.

The consulted OEIS entry still labels the leading asymptotic conjectural, and
the cited Guttmann–Kotěšovec paper presents numerical analysis. A targeted
literature search did not locate an earlier proof of this specific asymptotic;
that search does not establish a comprehensive priority claim.

This is a research manuscript with conventional proofs and executed checks.
It has not undergone independent peer review or Lean/Rocq formal verification.
No change was made to the ProveIt repository or to OEIS.
