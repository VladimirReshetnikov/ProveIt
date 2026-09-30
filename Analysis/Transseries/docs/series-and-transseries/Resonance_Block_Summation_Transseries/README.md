# Resonance-Block Summation of Transseries

**Small divisors, coalescing Stokes actions, and nonlinear inversion**

Research report prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

Open `article.pdf`. Its editable, self-contained LaTeX source is `article.tex`.
Keep the `results/` directory beside the source when rebuilding: the source
inputs `results/coalescence_table.tex`.

The report studies the meromorphic Borel kernels

    Fhat(t) = t^d / product_j sin(pi omega_j t),  omega_j > 0.

Its main results are:

1. A uniformly normally convergent Stokes representation using blocks of at
   most d nearby pole occurrences, with explicit separation-independent norms
   and an action-cutoff tail bound.
2. The exact raw-residue convergence abscissa for two irrationally related
   lattices, including an explicit example where the raw series fails at
   every positive argument despite exact Gevrey order one.
3. Uniform coalescence profiles, exact double/triple residues, and a
   rational-exponential compression criterion.
4. Certified nonlinear inverse transport in the block norm, with separate
   action and amplitude truncation errors; a finite inverse coefficient
   formula at every action and its analytic finite-cut realization.
5. An abstract bounded-cluster criterion and twelve further research projects.

## Mathematical status

The report supplies conventional proofs. It does not claim Lean verification,
a named community-wide conjecture resolution, or established research priority
for every refinement. Classical Borel-Laplace summation, divided differences,
and Lagrange inversion are credited. The central contribution is a quantitative
finite-lattice/finite-cluster package, not a general theory of arbitrary
countable-action resurgence.

The comparison to ProveIt is specific: its weighted countable inverse theorem
requires a sum of individual analytic norms. In the present examples that sum
can fail even the term test. The report proves bounds after cancellation in
finite blocks, thereby supplying admissible data for the analytic inverse
method. It does not claim the general inverse formula itself is new.

The raw convergence boundary is not classified. The inverse's full Borel-sheet
structure, infinitely many period lattices, and global inverse univalence are
not claimed. The raw formal action expansion is not asserted to converge
numerically at fixed argument; the block-indexed representation is the
convergent one.

## Reproduce

Use Python 3.10 or newer and a TeX Live installation with the packages listed
in `article.tex`. The recorded run used Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0,
and pdfLaTeX.

```sh
python -m pip install -r requirements.txt
sh build.sh
```

The stages can also be run separately:

```sh
python verify.py --stage symbolic
python verify.py --stage numeric
python verify.py --stage tables
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The program uses no network access or external datasets. It writes generated
files only under the local `results/` directory. The build additionally creates
ordinary local TeX auxiliary files and logs.

Since the editorial amendments below, `build.sh` no longer overwrites the
recorded results: it runs `verify.py --stage all --outdir build/results`, writes
its pass logs and TeX auxiliary files to `build/`, typesets the article from the
recorded `results/coalescence_table.tex`, and replaces only `article.pdf`. Set
`PYTHON` to choose the interpreter. The separate `verify.py` stages above still
write into `results/` (including the table the article inputs, and the Python
version recorded in `verification.json` and `verification.txt`); use `--outdir`
or a copy to compare with the recorded files.

## Executed checks

The distributed results record 36 exact symbolic assertions and 15 numerical
assertions, all passing. Contour checks use 90 decimal digits; near-collision
reference calculations use 200 digits. A separate 50-digit demonstration
compares the unstable raw residue formula with the stable pair formula.
Recorded values are rounded for serialization, not stored at full internal
working precision.

These checks are **not directed-rounding interval certificates** and do not
replace the mathematical proofs. The analytic tail bound is proved in the
article; its numerical evaluation in the script is ordinary high-precision
floating-point arithmetic.

## Contents

- `article.tex`, `article.pdf`: article source and rendered report.
- `verify.py`: complete symbolic and numerical checking program.
- `results/`: actual recorded checks and generated table source.
- `requirements.txt`, `build.sh`: dependencies and build command.
- `SOURCES.md`: repository and primary-literature provenance.
- `QA_REPORT.md`: compilation and visual-inspection record.
- The delivered checksum ledger was verified in full on filing (batch 48) and
  not kept; the delivered archive remains in the repository history (see
  `docs/incoming/README.md`, batch 48 row).

No repository files were changed. No external source corpus or font files are
included.

## Editorial amendments (ProveIt, 2026-09-29)

Made in place after filing (batch 48 of `docs/incoming/README.md`). The author's
text is otherwise unchanged; every change to the article source is preceded by a
`% ed. (2026-09-29)` comment, and no label was renamed or theorem renumbered.

- `article.tex`: two visible "Editorial note (ProveIt, 2026-09-29)" blocks. At the
  start of Section 1, a scope note: the title is broader than the results, which
  concern the sine-product kernels (plus the hypothesis-bound
  `prop:abstract`), and its "resonances" are near-coincident Borel poles. In
  Section 1.2: the report answers, without citing it, the forward half of the
  research question "Countably many resurgent input poles" of
  `../Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex`; the resurgent
  half stays open (project 6). The abstract is unchanged. The title page no longer
  carries a PDF page anchor (`\hypersetup{pageanchor=false}`), which removes a
  pre-existing duplicate-destination warning.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`; 26 pages (the
  delivered PDF had 25; `QA_REPORT.md` describes the delivered build), no errors,
  undefined references, multiply defined labels or duplicate destinations.
- `verify.py`: writes LF on every platform, and accepts `--outdir` (default
  unchanged).
- `build.sh`: redirected to `build/` as described under "Reproduce". Tested on a
  copy (SymPy 1.14.0, mpmath 1.3.0): the six files in `build/results/`, and the six
  written by a default `verify.py --stage all`, are byte-identical to the filed
  `results/`.
- This README: the paragraph on `build.sh`, and the checksum-ledger entry.

### Batch-52 cross-reference notes (ProveIt, 2026-09-29)

Added when batch 52 was filed; marked in the source by a
`% ed. (2026-09-29, batch 52)` comment.

- `article.tex`: an editorial note after research Question 1 ("The boundary
  of the raw-series half-plane"): answered by
  `../Critical_Line_Continued_Fractions_Riesz_Summation/` (batch 52) for two
  lattices with numerator `t^D`, `D >= 2` (this report's kernel is
  `d = D = 2`). With `A_k = q_k^D q_(k+1) e^(-b q_k)` on `Re z = b = beta(alpha)`:
  increasing-action convergence exactly when `A_k -> 0`, absolute exactly
  when `sum A_k < infinity`, the separately indexed sums exactly when
  `sum (-1)^(p_k+q_k+k) A_k e^(-i q_k Im z)` converges, with an
  increasing-action sum whose separate sums diverge (`thm:classification`,
  `ex:opposite`); absolute, conditional and term-test-failing behaviour at
  every prescribed positive abscissa (`cor:types`). For `d` lattices, Riesz
  means of integer order `m >= d - 1` recover the block sum on `Re z > 0`
  with an exact finite derivative bias and no Diophantine condition
  (`thm:riesz`), and `d - 1` is minimal for period-uniform bounds
  (`thm:sharp`).
- `article.pdf`: rebuilt (`latexmk -pdf`; 26 pages, unchanged; no errors,
  undefined references, multiply defined labels or duplicate destinations).
  `QA_REPORT.md` still describes the delivered build.
- `README.md`: this subsection.
