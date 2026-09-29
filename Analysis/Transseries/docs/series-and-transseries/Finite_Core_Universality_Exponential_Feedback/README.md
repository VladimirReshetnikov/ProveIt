# Finite-Core Universality and Sharp Large Order
## Countable exponential-feedback transseries

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

The 27-page article studies the formal equation

    U(q) = sum_{j>=1} q^j exp(a j^p U(q)),  a>0, p>1,

and nonnegative perturbations of finitely many initial weights and slopes,
with the first primitive weight fixed at one.

## Main results

The coefficient contribution of exactly one action above a finite analytic
core of size M is asymptotic to the full coefficient if and only if
M(p-1)>1. At or below the boundary its relative contribution tends to zero.
The paper gives a full multiplicative saddle formula, conditional local
Gaussian fluctuations and an unconditional central limit theorem, an explicit
quadratic correction, a coefficient-ratio and least-formal-term law, and sharp
formal inverse asymptotics in the superquadratic range p>2.

All proofs are conventional mathematics. No Lean verification or exhaustive
originality/priority certification is claimed. The proposed quadratic inverse
equivalent is explicitly a conjecture, not one of the proved results.
(Editorial, 2026-09-29: two later packages each claim a proof of it; see
"Editorial amendments" below.)

## Files

- `article.pdf` and `article.tex`: compiled article and self-contained source.
- `code/verify_exact.py`: standard-library exact arithmetic, independent
  partition and marking comparisons, and inverse-composition residual checks.
- `code/diagnostics.py`: NumPy/SciPy positive log recurrence and finite-core
  nonlinear saddle calculations.
- `code/report_tables.py`: table generation and exact-versus-floating cross-checks.
- `data/`: exact integer-normalized CSV coefficients, numerical CSV/NPZ data,
  JSON reports, and generated table rows.
- `PROOF_STATUS.md`: boundaries and proof dependencies.
- `SOURCES.md`: repository provenance and primary literature.
- `requirements.txt`, `Makefile`: reproduction aids.

## Build the article

The source embeds its bibliography and all tables, so it compiles without
running Python or downloading repository files. Use a TeX installation with
standard mathematical packages, Latin Modern, xurl, hyperref and bookmark.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

A third pass can be used if TeX reports changed cross-references. `make` runs
three passes. No external font files are included or required by the package.

## Reproduce the calculations

Use Python 3.10 or later. Exact calculations need only the standard library.

```sh
python code/verify_exact.py --order 300
python -m pip install -r requirements.txt
python code/diagnostics.py --order 1000 --powers 2 3
python code/report_tables.py
```

The numerical driver is primarily tested on p=2 and p=3. For p close to one,
its automatically selected core can become large, and a moderate n may lie
outside the small-branch regime. Such a solver failure is not a contradiction
of the fixed-parameter asymptotic theorem.

## Recorded verification

For a=1 and p=2,3, exact coefficients and inverse coefficients were computed
through degree 300. All 36 independent partition checks, 96 independent
one-tail marking checks, and 598 inverse-composition residual checks passed.
The residual checks are not a separate independent algorithm for inversion.

Positive log-domain coefficients were computed through degree 1,000.
Agreement with the exact coefficients through degree 300 was within 9.1e-13
in absolute log discrepancy in the recorded run. These are floating-point
diagnostics, not interval certificates. Numerical asymptotic agreement does
not prove the article's limit theorems.

The exact CSV columns contain **n! times** ordinary coefficients. Divide by
n! to recover u_n or v_n. Negative inverse values are retained with their signs.

No ProveIt repository file, branch, issue, or pull request was modified.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 47 (see `docs/incoming/README.md`). The
following changes were made on 2026-09-29; everything else is as delivered.

- `article.tex`: six visible "Editorial note (ProveIt, 2026-09-29)"
  paragraphs (an unnumbered environment, so the article's own numbering is
  unchanged), each preceded by a `% ed. (2026-09-29)` comment:
  after Theorem `thm:cutoff` (the Poisson-layer package sharpens the
  boundary case `M(p-1)=1`); after Theorem `thm:explicit` (the
  microscopic-condensation package proves `eq:quadratic` independently at
  `a = 1`); at the end of "The exact point where the proof stops" (the
  weighted-type package settles the n-th-root scale of the inverse for
  `1 < p <= 2` in limsup form, and does not decide the conjecture); after
  Conjecture `conj:quadratic-inverse` (two independent claimed proofs,
  unreviewed, in `../Quadratic_Exponential_Feedback_After_Reversion/` and
  `../Signed_Quadratic_Feedback_Inversion/`, with their hypotheses and the
  agreement of their exact coefficients; the conjecture is kept as stated);
  and in the research questions on critical logarithmic boundaries and on
  joint laws of the background cloud (partial answers in the Poisson-layer
  and microscopic-condensation packages). Five bibliography entries
  `ed:mic`, `ed:plb`, `ed:swt`, `ed:qef`, `ed:sqf` were added, and the
  bibliography's widest label was widened from `9` to `99`. No existing
  label was renamed or removed.
- `article.pdf`: rebuilt from the amended source (27 pages; the delivered
  PDF had 26). Line numbers of `article.tex` after the first insertion
  point differ from those of the delivered file.
- `code/verify_exact.py`, `code/diagnostics.py`, `code/report_tables.py`:
  the CSV writers now pass `lineterminator='\n'` and the JSON/table
  writers `newline='\n'`, so a rerun on any platform emits LF, like the
  filed files. The three programs were rerun on a copy with the commands
  above (sympy 1.14.0, mpmath 1.3.0, numpy 2.3.5, scipy 1.17.0, Windows):
  `exact_p2.csv`, `exact_p3.csv`, `inverse_diagnostics.csv`,
  `cross_checks.json` and both `table_*.tex` were byte-identical to the
  filed files. `exact_verification.json` and `numerical_verification.json`
  differ in their `runtime_seconds` field, which records wall-clock time
  and varies from run to run. `numerical_verification.json`,
  `saddle_diagnostics.csv` and `core_cutoff_table.csv` also differ in the
  last one or two digits of floating-point diagnostics (relative
  differences at most 2e-12), and `log_coefficients_p2.npz` in two array
  entries by one unit in the last place; the `.npz` archives also record
  the creating platform. The filed data files are the recorded run and were
  not replaced.
- `README.md`: the page count (26 to 27), the parenthetical pointer after
  "Main results", and this section.
