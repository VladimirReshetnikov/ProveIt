# Strict Conditioning Order for Fabius Observation Masks

This companion (six pages since the editorial amendments below; five as
delivered) proves strict total-variation ordering when a larger observed cap replaces a smaller one, comparing an original uniform product conditioned below a threshold with a common exponential tilt. Positive summable caps, arbitrary real tilt, positive-probability conditioning, and finite/countable common observations are allowed, even when no hidden coordinates remain.

For one exchange, equality occurs exactly for equal caps, or zero tilt with vacuous conditioning. For finite masks of equal size admitting a cap-dominating matching, equality in the nontrivial model occurs exactly when the cap multisets agree.

In the Fabius convention, this gives overlap_late < overlap_early for every 0<q<1, rho>0, n>=2 and 1<=m<n, including arbitrary common outside observations. The names refer to the hidden blocks; the late-hidden mask observes larger caps.

## Contents

- `strict_fabius_conditioning_order.pdf`: complete report
- `strict_fabius_conditioning_order.tex`: editable LaTeX source
- `build.sh`: ordinary three-pass TeX Live build
- `checks/verify_strictness_exact.py`: Python standard-library exact rational checker
- `checks/strictness_exact.json`: 98,956 strict-level comparisons, 396 normalized affine profiles and the exact generic equality counterexample
- `SOURCES.md`, `validation.json`, `SHA256SUMS`: source context and artifact verification (`SHA256SUMS` retired on filing; not in the repository)

Run `python3 checks/verify_strictness_exact.py` for the regression checks and `bash build.sh` to rebuild the PDF. (Since the editorial amendments of 2026-10-01 below, the checker writes to
`checks/rerun/`; `build.sh` runs `pdflatex` in this directory and overwrites the
filed PDF, so build on a copy.) The mathematical proof, not finite testing, establishes the universal statements.

This is a fixed-conditioning comparison. It does not assert one kernel for all weights, strictness for every divergence generator, or unrestricted noise extensions. The companion leaves preceding reports unchanged. It makes no worldwide priority claim and is neither formally verified nor externally refereed.

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

- `strict_fabius_conditioning_order.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Two notes:
  - after the proof of Corollary 4.2: it contains Corollary 4.1 of
    `../Exact_Fabius_Mask_Order/` (strict for `q = 1/M`, `1 <= rho < M`,
    `n >= 3`), and it makes the comparison of
    `../Second_Order_Critical_Complements_Fabius_Conditioning/` (its
    Corollary 3.3: same model, masks and superscripts, strict for all
    sufficiently large `n` when `m / log n -> c` in `(0, infinity)`) hold at
    every `n >= 2` and `1 <= m < n`, without affecting its limit; for
    `delta n <= m <= (1 - delta) n` Corollary 5.2 of
    `../Proportional_Fabius_Mask_Edgeworth/` gives the difference
    `phi(c) c D(q, rho) / m + O(n^{-3/2})`;
  - at the end of Section 5, a series map: the eight notes in the order
    written (this is the seventh); `Nonstrict` (source
    `exact_fixed_conditioning_order.tex`) is
    `../Exact_Fixed_Conditioning_Order/`, and `Repository` is
    `../Critical_Complements_Sharp_Information_Loss/`.
- `strict_fabius_conditioning_order.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29): 6 A4 pages (5 as delivered), 338,173 bytes; all 18
  fonts embedded, none Type 3; the final log has no error, overfull or
  underfull box, undefined or multiply defined reference, duplicate
  destination, or rerun request. The pages carrying the notes were rendered
  and inspected.
- A reciprocal note of 2026-10-01 now stands after Corollary 3.3
  (`cor:comparison`) of
  `../Second_Order_Critical_Complements_Fabius_Conditioning/`, and (added in
  the editorial pass after batch 72) a second one after the batch-71 note on
  the first question of Section 13 of
  `../Critical_Complements_Fabius_Conditioning/`, whose block comparison is
  the same one (the observed block `{r+1, ..., n}` against the prefix).
- `checks/verify_strictness_exact.py`: new option `--output-dir`.
  As delivered, the program overwrote the recorded file beside itself, with
  CRLF line endings on Windows; it now writes `checks/rerun/strictness_exact.json` (or
  `<output-dir>/strictness_exact.json` with `--output-dir`), with LF line endings. Pass
  `--output-dir` with the program's own directory, on a copy, to regenerate
  the recorded file. On the ProveIt machine use `py` rather than `python3`.
  A rerun of the amended checker on a copy (2026-10-01,
  `py checks/verify_strictness_exact.py`, Python 3.14.4, standard library)
  wrote `checks/rerun/strictness_exact.json` equal to the recorded file byte
  for byte.
- `build.sh`: kept as delivered. It runs `pdflatex` three times in this
  directory, so it overwrites the filed PDF and leaves `.aux`, `.log` and
  `.out` files here: build on a copy.
- `validation.json`: `pages` set to 6; its other entries are as delivered.
- `README.md`: the page count, the retired ledger under "Contents", the
  parenthesis after the reproduction command, and this section.
