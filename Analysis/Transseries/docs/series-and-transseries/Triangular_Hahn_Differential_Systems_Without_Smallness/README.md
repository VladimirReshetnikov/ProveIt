# Triangular Hahn Differential Systems Without Smallness

**Rank-one descent, exact logarithmic degree, and finite residue certificates**

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

- `triangular_hahn_systems.pdf`: the compiled 25-page A4 article.
- `triangular_hahn_systems.tex`: editable LaTeX source, including bibliography.
- `verification/summary.tex`: generated verification table, also embedded in the article source.

## Main results

The base field is the full real Hahn field with real powers of x and a fixed
finite number of iterated logarithms, lexicographically ordered by growth.
The system is triangular, or a triangularizing gauge over that field is supplied.
Its coefficients and strictly triangular couplings have **no smallness assumption**.

Theorem 3.2 gives an explicit rank-one split/nonsplit criterion. Split factors
have one residue obstruction; nonsplit scalar factors are bijective on the base
field. Theorem 3.4 proves that increasing finite logarithmic depth cannot create
a new homogeneous rank-one mode.

Theorem 4.2 proves that all solutions in the entire finite logarithmic tower
already depend polynomially on one additional logarithm. The degree is bounded
by the number of split vertices on a dependency path, not by coefficient size.

Theorems 6.1–6.2 construct a finite formal residue matrix M(z), with diagonal z
and determinant z^r. Its Smith exponents classify the homogeneous degree
filtration and the exact minimum degree for every base-field forcing.
Theorem 7.2 gives finite jets and positive/negative rational matrix certificates
when the relevant coefficient operations are available exactly.

Sections 8–9 provide a three-coordinate mixed example. A nonsplit intermediate
coordinate transports a residue; a direct coupling cancels it at c = 1. The
minimum forced degree changes from 2 to 1. Actual real solutions and explicit
signed factorial-series error bounds are proved for this example.

Nine further research directions are developed in Section 12.

## Relationship to ProveIt and novelty boundaries

The target is the logarithmically-small perturbation and matrix-system questions
in `Exact_Logarithmic_Degree_Smith_Invariants/exact_logarithmic_degree.tex`.
That predecessor uses an outer-small scalar operator class. The present paper
replaces smallness by triangularity, includes split and nonsplit diagonal
factors together, and classifies all finite logarithmic depths.

Normalized Hahn integration, finite-defect elimination, Smith normal form,
Toeplitz matrices, and classical exponential-integral asymptotics are credited
rather than claimed as new. The proposed contribution is their unrestricted
triangular realization, rank-one descent, path-sensitive bounds, finite-word
certificates, and the mixed transport example. Global publication priority has
not been established.

These are conventional written proofs, not a Lean formalization or an
independently refereed publication. The article does not decide triangularizability,
solve arbitrary nontriangular systems, implement arbitrary infinite Hahn data,
or prove analytic summability for the general class.

## Verification

Recorded environment: Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0.
Python 3.10 or later is required by the source syntax.

```sh
python -m pip install -r verification/requirements.txt
python verification/verify.py
```

On Windows, `py` may be used instead of `python`.

The recorded run passed **1,413 exact rational/symbolic assertions**, including
20 finite-defect models, 29 Jordan profiles with paired degree certificates,
20 general triangular polynomial matrix-series cases, and five specializations
of the mixed example. It also passed 36 high-precision numerical illustrations
of the analytic bounds. The numerical checks are not interval arithmetic.

The script writes to `rerun/` by default and does not overwrite the recorded
files. It supports `--output-dir PATH` and `--skip-numerical`.
A repeated full run in the recorded environment reproduced `results.json`
byte for byte. Finite experiments do not establish the arbitrary-support
statements; those depend on the article's proofs.

## Build

From this directory:

```sh
sh build.sh
```

The script runs pdfLaTeX three times, using `build/` for temporary files, then
copies the final PDF to the package root. A standard TeX Live or MiKTeX setup
with the packages named in the preamble is sufficient. The bibliography is
embedded. No private fonts, network access, repository checkout, or external
figures are required once dependencies are installed.

On a system without a POSIX shell, run `pdflatex -interaction=nonstopmode
-halt-on-error triangular_hahn_systems.tex` three times from this directory.
The main TeX source is self-contained: its verification table and bibliography are embedded. Rerunning the checks does not rewrite the article source.

## Additional files

`notes/proof_audit.md` records the hypotheses and highest-value review points.
`notes/repository_provenance.json` records the pinned source paths and identifiers.
`notes/validation.json` records compilation, rendering, and verification checks.
`SHA256SUMS.txt` records hashes of the delivered package files except itself.

Repository snapshot: `47e1a335d252b90809a5416a6438d7aa1e087770`.
No repository files were changed or uploaded.
