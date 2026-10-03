# Triangular Hahn Differential Systems Without Smallness

**Rank-one descent, exact logarithmic degree, and finite residue certificates**

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

- `triangular_hahn_systems.pdf`: the compiled 27-page A4 article (25 pages as
  delivered; rebuilt with editorial notes, see the last section).
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

On Windows, `py` may be used instead of `python`, or
`uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python verification/verify.py`.

The recorded run passed **1,413 exact rational/symbolic assertions**, including
20 finite-defect models, 29 Jordan profiles with paired degree certificates,
20 general triangular polynomial matrix-series cases, and five specializations
of the mixed example. It also passed 36 high-precision numerical illustrations
of the analytic bounds. The numerical checks are not interval arithmetic.

The script writes to `rerun/` by default and does not overwrite the recorded
files. It supports `--output-dir PATH` and `--skip-numerical`. (Editorial,
2026-09-29: it now refuses an `--output-dir` that is `verification/` itself
unless `--overwrite-recorded` is also given. `rerun/` is not ignored by the
repository's `.gitignore`; delete it after a run.)
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
`notes/validation.json` records compilation, rendering, and verification checks;
its page count, sizes, word count and the two SHA-256 digests of the article
source and PDF were recomputed for the editorial rebuild of 2026-09-29 (see
below).
The delivered checksum ledger `SHA256SUMS.txt` was verified in full on filing
(11/11, batch 53) and not kept; the delivered archive remains in the
repository history (see `docs/incoming/README.md`, batch 53 row).

Repository snapshot: `47e1a335d252b90809a5416a6438d7aa1e087770`.
No repository files were changed or uploaded.

## Editorial amendments (ProveIt, 2026-09-29)

Filed on 2026-09-29 (batch 53 of `docs/incoming/`; see `docs/incoming/README.md`).
The following changes were made; every change to the article source is
preceded by a `% ed. (2026-09-29)` comment, every visible addition is an
unnumbered "Editorial note (ProveIt, 2026-09-29)" or a bibliography entry
marked "Editorial addition", and no label was renamed or theorem renumbered.

- `triangular_hahn_systems.tex`:
  - preamble: an unnumbered `ednote` environment;
  - end of Section 1.1: the exact-degree questions answered here are the
    residue-obstruction article's "Perturbations small only in logarithms"
    and "Matrix systems and nonreal indicial roots"
    (`../Residue_Obstructions_Logarithmic_Depth_Promotion/`); for first
    order, `thm:rankone` and `thm:descent` settle its classification of
    coefficients in negative powers of `log x` (split exactly when no
    exponent lies in `(0,1)`; no further depth ever helps), and
    `thm:triangular`/`cor:gauge` extend it to operators that factor over
    the field, not to those that do not; the Hahn–Fuchsian package's
    depth-0 invariant (nilpotency index of `B`); and three batch-52
    packages this article did not see:
    `../Path_Sensitive_Small_Divisors_Hahn_Fuchsian/` (its `lem:leading`,
    path-kernel degree = number of exact resonances, the depth-0
    independent-coefficient counterpart of the bound `q`; its independence
    hypothesis excludes the cancellation of `prop:mixed`),
    `../Nonlinear_Hahn_Dulac_Finite_Resonance_Control/` and
    `../Nonlinear_Hahn_Fuchsian_Algebraic_Convergence_Loci/` (nonlinear, not
    triangular);
  - after Example `ex:threshold`: for `x^(-1)(λ + Σ_(k≥1) c_k L^(-k))`, the
    predecessors' first target, the split criterion holds at every depth
    `n ≥ 1` with integrating factor `x^λ L^(c_1) exp(I_n b)`; with real
    exponents the coefficient is nonsplit exactly when a term `L^(-α)`,
    `0 < α < 1`, or a positive power of `L` occurs;
  - three bibliography entries `ed:psh`, `ed:nhd`, `ed:ncl`, after the
    delivered ones.
- `triangular_hahn_systems.pdf`: rebuilt with three pdfLaTeX passes (27
  pages, was 25; no errors, undefined references, multiply defined labels,
  duplicate destinations, LaTeX warnings, overfull or underfull boxes; no
  Type 3 font).
- `notes/validation.json`: `pdf_pages`, `pdf_bytes`, `tex_bytes`,
  `tex_source_whitespace_words` and both `article_sha256` digests
  recomputed for the filed source and PDF (they match them), and an
  `editorial_rebuild` field added recording the delivered values; the
  `build` and `visual_review` fields describe the delivered build. Any
  later rebuild makes the PDF digest stale, since pdfTeX embeds the build
  date.
- `verification/verify.py`: a guard refuses `--output-dir` equal to
  `verification/` unless `--overwrite-recorded` is given (the default,
  `rerun/`, was already safe). A rerun of the amended program on a copy
  (Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0) reproduced
  `verification/results.json` and `verification/summary.tex` byte for byte
  (1,413 exact assertions, 36 numerical illustrations); the guard was
  exercised and wrote nothing.
- `README.md`: this section, the page count, the Windows recipe, the
  `rerun/` and guard note, and the `notes/validation.json` and ledger
  sentences.
