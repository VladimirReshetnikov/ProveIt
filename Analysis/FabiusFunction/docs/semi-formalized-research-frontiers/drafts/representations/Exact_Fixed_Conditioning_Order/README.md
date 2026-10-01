# Exact Conditioning Order for Fabius Observation Masks

This six-page research note proves a fixed-weight comparison for independent common-tilt uniform coordinates on summable caps. Any cap-dominating injection between observation masks gives convex order of the projected likelihood ratios, a binary Blackwell kernel, and every f-divergence inequality. The weight is bounded, nonnegative and log-concave, with positive expectation. Finite/countable and overlapping masks are included.

For the original uniform product conditioned below any admissible threshold, the hypothesis holds. In the repository's Fabius convention, this proves overlap_late <= overlap_early for every 0<q<1, rho>0, n>=2 and 1<=m<n. The names refer to the hidden blocks; the late-hidden mask observes the larger caps.

The kernel may depend on the fixed weight. All inequalities are nonstrict. Arbitrary independent noise is not covered without an effective-profile hypothesis. This does not replace the arithmetic classification for a single kernel valid for all weights.

## Files and reproduction

- `exact_fixed_conditioning_order.pdf`: complete mathematical report
- `exact_fixed_conditioning_order.tex`: editable LaTeX source
- `build.sh`: three-pass build with an ordinary TeX Live installation
- `checks/verify_rectangle_exact.py`: standard-library exact rational verification
- `checks/rectangle_exact.json`: 18,083 rectangle comparisons on 5,115 sign profiles and 29,928 level-trapezoid comparisons, all passing
- Other scripts and JSON: finite-product exploratory checks using NumPy and SciPy; they support normalization and orientation, and do not prove the theorem
- `SOURCES.md`, `validation.json`, `SHA256SUMS`: references and artifact verification (`SHA256SUMS` retired on filing; not in the repository)

Run `python3 checks/verify_rectangle_exact.py` for the exact checks. The optional numerical scripts write their result JSON beside themselves. Run `bash build.sh` to rebuild the PDF. (Since the editorial amendments of 2026-10-01 below, every script writes to
`checks/rerun/` instead; `build.sh` runs `pdflatex` in this directory and
overwrites the filed PDF, so build on a copy.)

The continuous and countable statements are proved in the manuscript. The proof uses classical marginalization, convex-order and martingale-coupling results and makes no worldwide priority claim. It is not formally verified or externally refereed.

## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
The eight notes of the series are filed beside one another, in the order
written: `../Exact_Fabius_Mask_Order/`, `../Universal_Garbling_Classification/`,
`../Universal_Fabius_Mask_Criterion/`, `../Uniform_Smoothing_Mask_Stabilization/`,
`../Arithmetic_Geometric_Mask_Order/`, `../Exact_Fixed_Conditioning_Order/`,
`../Strict_Fabius_Conditioning_Order/`, `../Proportional_Fabius_Mask_Edgeworth/`.

- `exact_fixed_conditioning_order.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Two notes:
  - after the proof of Corollary 4.1: the next note,
    `../Strict_Fabius_Conditioning_Order/`, makes (15) strict for total
    variation (its Corollary 4.2, same `q`, `rho`, `n`, `m`, also with common
    observations) and recalls Lemma 2.1 in its Section 2; for `q = 1/M`, (15)
    had been proved by `../Exact_Fabius_Mask_Order/` (its (12)) with one
    residue kernel for every total-sum reweighting; the comparison of
    `SecondOrder` that the corollary strengthens is its Corollary 3.3;
  - at the end of Section 5, a series map: the eight notes in the order
    written (this is the sixth); `SecondOrder` (source
    `Second_Order_Fabius_Crossover.tex`) is
    `../Second_Order_Critical_Complements_Fabius_Conditioning/` (batch 71,
    filed before the commit pinned here), `Arithmetic` is
    `../Arithmetic_Geometric_Mask_Order/`, and `Repository` is
    `../Critical_Complements_Sharp_Information_Loss/`.
- `exact_fixed_conditioning_order.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29): 6 A4 pages, as delivered, 351,280 bytes; all 18
  fonts embedded, none Type 3; the final log has no error, overfull or
  underfull box, undefined or multiply defined reference, duplicate
  destination, or rerun request. The pages carrying the notes were rendered
  and inspected.
- `checks/verify_rectangle_exact.py` and the seven `checks/probe_*.py`: new
  option `--output-dir` in each.
  As delivered, the program overwrote the recorded file beside itself, with
  CRLF line endings on Windows; it now writes `checks/rerun/<name>.json` (or
  `<output-dir>/<name>.json` with `--output-dir`), with LF line endings. Pass
  `--output-dir` with the program's own directory, on a copy, to regenerate
  the recorded file. On the ProveIt machine use `py` rather than `python3`.
  Reruns of the amended programs on a copy (2026-10-01):
  `py checks/verify_rectangle_exact.py` (Python 3.14.4) wrote
  `checks/rerun/rectangle_exact.json` equal to the recorded file byte for
  byte; with `uv run --no-project --with numpy --with scipy python` (Python
  3.13.5, NumPy 2.5.3, SciPy 1.18.1, 5 to 52 seconds each, run from
  `checks/`), `probe_masks.py`, `probe_other_thresholds.py`,
  `probe_stoploss.py`, `probe_bands.py`, `probe_sign_pattern_unbalanced.py`
  and `probe_sign_pattern.py` each reproduced its recorded JSON byte for byte.
  `probe_singletons.py` stops, as delivered, at its own precision guard
  (`ArithmeticError`): the probes compute in `np.longdouble`, which is the
  64-bit double on Windows, and need an extended-precision `long double`
  (x86-64 Linux, for example), so `singleton_probe.json` (1,050 cases) was not
  reproduced here. The probes are exploratory and are not certificates; they
  need NumPy and SciPy, which no requirements file pins.
- `build.sh`: kept as delivered. It runs `pdflatex` three times in this
  directory, so it overwrites the filed PDF and leaves `.aux`, `.log` and
  `.out` files here: build on a copy.
- `validation.json`: unchanged (the page count is still 6).
- `README.md`: the retired ledger under "Files and reproduction", the
  parenthesis after the build command, and this section.
