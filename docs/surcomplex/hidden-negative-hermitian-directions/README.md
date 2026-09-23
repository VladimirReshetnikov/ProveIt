# Hidden Negative Directions in Surcomplex Linear Algebra
## Prime-denominator approximation barriers and a two-scale matrix-measure criterion

Research manuscript prepared for Vladimir Reshetnikov, 22 September 2026.
The PDF has 25 physical pages: title, two contents pages, and 22 numbered pages.

## Contents

- `article.tex`: standalone LaTeX source with internal bibliography.
- `article.pdf`: compiled article with linked references and contents.
- `code/verify.py`: exact finite diagnostics, with an optional JSON output mode.
- `data/verification.json`: recorded structured diagnostic results.
- `data/verification.txt`: recorded human-readable diagnostic results.
- `data/build_report.json`: compilation and PDF validation summary.
- `source_audit.md`: compact provenance, claim, and limitation ledger.
- `requirements.txt`: Python dependency for the diagnostic script.
- `build.sh`: PDF build command, independent of the calling directory.

## Theorem guide

The numbering and page references below are the article's printed page numbers.

| Result | Location | Content |
|---|---|---|
| Uniform approximation barrier | Theorem 4.2, p. 6 | The prime tail differs from every finite-lattice-supported series at valuation below delta. |
| Exact primorial approximation law | Theorem 4.3, p. 7 | Crossing the Nth prime-tail exponent requires and admits field degree equal to the product of the first N primes. |
| Simultaneous valuation separation | Theorem 5.1, p. 8 | Almost-disjoint prime tails have a uniform noncancellation bound for arbitrary finite-lattice coefficients. |
| Algebraic independence | Theorem 5.2, p. 9 | One explicit continuum-sized family is algebraically independent over the entire finite-lattice field. |
| Maximal hidden negative inertia | Theorem 6.1, p. 10 | A matrix of size r+1 has inertia (1,r,0), yet is strictly positive on all nonzero finite-lattice probe vectors. |
| Persistence through closure | Theorem 7.1, p. 11 | The same vector-probe obstruction survives valuation closure; rational exponents give the Levi-Civita case. |
| Actual surreal transport | Theorem 8.2, p. 14 | The construction works in No[i] and is insensitive to adding finitely many monomial scales to a probe. |
| Exact two-scale matrix criterion | Theorem 9.2, p. 14 | A residual compression and an annihilation condition characterize P + epsilon Q >= 0. |
| Matrix-measure null ideals | Theorem 10.1, p. 17 | Two ordinary absolute-continuity conditions characterize a positive two-scale matrix measure. |

The probe-field construction, character actions, finite Hermitian spectral theory,
and qualitative density obstruction are background, not originality claims.

## Build

A TeX distribution needs `pdflatex`, `latexmk`, `newtx`, `amsmath`, `amsthm`,
`mathtools`, `geometry`, `microtype`, `booktabs`, `enumitem`, `fancyhdr`,
`tcolorbox`, `hyperref`, and `xurl`, with their dependencies.

From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Or run `./build.sh`. Without latexmk, run pdflatex three times with the same flags.
No external bibliography file, custom font file, image, network access, or
shell escape is required. Font files are not included in the archive.

## Reproduce the exact checks

```sh
python -m pip install -r requirements.txt
python code/verify.py
python code/verify.py --json
```

The program prints results and does not overwrite the recorded files.
It uses exact arithmetic, never a numerical substitute for an infinitesimal.
The recorded environment was Python 3.13.5 and SymPy 1.14.0.
All tests passed: 5,946 matrix pairs (1,823 positive) and 35,100 fresh-prime
nonmembership comparisons, plus symbolic matrix and finite character-orbit checks.

## Scope and status

The matrix positivity results concern restricted **vector probes**. Determinants
and principal minors immediately detect the negative matrices. Once the tail
entries are allowed as probe coordinates, the displayed negative vectors are
available. There is no undecidability or general algorithmic impossibility claim.

The approximation cost is field degree over C(t^delta), not expression length,
runtime, or a cost valid after changing the ground field.

The measure result uses coefficientwise countable additivity and exactly two
scales. It does not settle the arbitrary-support matrix-measure problem or supply
an infinite-dimensional spectral measure theorem.

The new assertions have written proofs but are not refereed or Lean-verified.
The checks are finite diagnostics, not proofs of the infinite assertions. Novelty
is provisional, based on a targeted audit of the repository snapshot
048b72cf7cbfc8ab246e4f73788c10460cb3f6e0 and relevant literature. No named published
conjecture is claimed settled, and no exhaustive priority search is claimed.
