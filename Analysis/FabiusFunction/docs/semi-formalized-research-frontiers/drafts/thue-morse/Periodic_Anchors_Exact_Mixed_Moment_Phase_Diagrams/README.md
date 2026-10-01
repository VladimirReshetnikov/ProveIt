# Periodic Anchors and Exact Mixed-Moment Phase Diagrams

Research article prepared for Vladimir Reshetnikov, 30 September 2026.

## Main contents

The 21-page article develops an exactly solvable class of mixed digital
products whose anchor phases form complete periodic orbits under x -> bx mod 1.
It proves an exact pressure formula and equilibrium-measure classification,
a global mixed-moment exponent for a squared shifted background, pure-product
leading asymptotics and critical windows, an exact seventh-root moment with
period-three leading amplitudes, a finite polyhedral pressure realization
theorem, and a nonlinear expanding-map extension. Eight further research
questions and a formalization roadmap are included.

The principal results concern this structured orbit-balanced class. The article
does not claim to solve arbitrary mixed phase tuples or the general single-phase
regularity problem. It does not rely on unreviewed pressure theorems from ProveIt.

## Files

- `article.pdf`: compiled article, 21 pages.
- `article.tex`: self-contained LaTeX source with inline bibliography.
- `figures/phase_diagram.pdf`: exact three-branch phase diagram.
- `figures/periodic_amplitude.pdf`: exact seventh-root residue-class amplitudes.
- `verify.py`: exact algebraic checks and separate numerical diagnostics.
- `verification_results.json`: reproducible numerical and exact-check output.
- `verification_run.txt`: console output from the executed checks.
- `requirements.txt`: Python dependencies for reproducing checks and figures
  (pinned since the editorial pass below to the versions in `environment.txt`).
- `environment.txt`: versions used for this build.

## Build the article

Run from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex article.tex` three times. No BibTeX or external
bibliography download is needed. The figure PDFs are already included; Python
is not needed to build the article. A standard TeX Live installation needs the
Libertinus, AMS, geometry, microtype, booktabs, graphicx, fancyhdr, titlesec,
enumitem, xurl, aliascnt, hyperref, and cleveref packages. No shell escape is used.

## Run verification

Use Python 3.10 or newer:

```sh
python -m pip install -r requirements.txt
python verify.py
```

Since the editorial pass (below) this writes `rerun/verification_results.json`
(LF line endings) and, with `--figures`, the two figures to `rerun/figures/`,
leaving the recorded files unchanged. To regenerate the recorded
`verification_results.json` and figures, run from this directory:

```sh
python verify.py --figures --out verification_results.json
```

Run `latexmk` again after regenerating figures to update the PDF. The exact
polynomial operations use Python integers in Z[eta], eta^2 + eta + 2 = 0.
The script verifies the finite norm tables and the seventh-root moment by exact
polynomial division for depths n=0,...,12 (largest N=4096). It also checks
coboundary identities and performs floating-point moment and critical-window
diagnostics. All exact assertions and numerical identity checks passed in the
recorded run.

The all-depth theorem follows from the proof in the article, not from a finite
list of computations. Numerical quadrature is not interval arithmetic; finite
moment estimates do not certify the limiting exponent, prefactor, or a spectrum.
At the triple point the finite-depth effective exponent converges noticeably
more slowly; the article explicitly records this rather than hiding the row.

## Provenance and status

Inspected ProveIt commit:

781594d886f8dc56069221e2b56bd1e94d9c6e5f

Relevant research index:

Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/README.md

The article distinguishes its derivations from prior single-phase pressure
work and from broader published pressure-flexibility results. It is an
unrefereed research draft with ordinary mathematical proofs, not a Lean
formalization. Worldwide priority has not been independently established.
The package makes no changes to the repository.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 66 to 68 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program and `requirements.txt`
`ed. (2026-09-30)`. The title-page and `pdfauthor` wording ("prepared with
ChatGPT") is kept as delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (no counter is shifted). One note,
  at the end of Section 1.1: the article bears on, but answers none of, four
  questions of the pressure articles beside it, "Nonatomic phases"
  (`../Thue_Morse_Critical_Pressure/`), "Regularity at nonzero phases" and
  "Other masks and multiple zeros" (`../Thue_Morse_Fractional_Pressure/`),
  and "Beyond one zero and beyond base two"
  (`../Thue_Morse_Integer_Pressure/`): it evaluates products of shifted
  masks whose phases fill complete periodic orbits, at fixed phases; a
  single mask whose phase has period at least two is not covered, and no
  phase regularity is proved. Each of those questions now carries a
  reciprocal note. With the single anchor `0`, Corollary 2.2 gives
  `B(max{1,a} - a)`, the atomic-phase values of the subcritical and
  fractional pressure articles.
- `figures/phase_diagram.pdf`, `figures/periodic_amplitude.pdf`: regenerated
  by the amended program (`python verify.py --figures`, on a copy) with
  TrueType instead of Type 3 fonts (Matplotlib `pdf.fonttype = 42`); the
  rendered figures are unchanged.
- `article.pdf`: rebuilt from the amended source and figures with `latexmk
  -pdf` (MiKTeX pdfTeX 1.40.29): 21 pages, as delivered, with no error,
  undefined reference, multiply defined label, duplicate destination or
  overfull box; every font is embedded and none is Type 3 (the delivered
  PDF had two Type 3 rows from the figures). The page carrying the note was
  rendered and inspected.
- `verify.py`: the default `--out` was `verification_results.json` in the
  current directory, so a plain run in this package overwrote the recorded
  file, and `--figures` the recorded `figures/`; it is now
  `rerun/verification_results.json` beside the program (figures to
  `rerun/figures/`). The JSON file is written with LF line endings on every
  platform, and the figures embed TrueType fonts. A rerun of the amended
  program on a copy (2026-09-30, `uv run --no-project --with numpy==2.3.5
  --with scipy==1.17.0 --with matplotlib==3.10.8 python verify.py
  --figures`) passed; 21 floating-point values differ from the recorded
  `verification_results.json` in their last digits, the largest relative
  difference (1.1e-5) being in a residual of size 1e-11
  (`coboundary.checks[1].maximum_scaled_error`).
- `requirements.txt`: the three dependencies are pinned to the versions
  recorded in `environment.txt` (they were unpinned).
- `README.md`: the run instructions, the requirements line, and this
  section. `verification_run.txt` is the console output of the delivered
  run, not a file the program writes.
