# Total Positivity and Cartwright Geometry

This report arrived on 2026-08-30 as the bare three-file directory
`drafts/incoming/Fabius_Total_Positivity_Frontier_Report/` and was filed in
`spectra-and-arithmetic/` by commit `1f2f7d26c`. The arrival SHA-256 values are
TeX `efea26060e6de63e97d00b982ca9e618f2234c88b8fd02f4ae9a8d63b7beecdd`,
PDF `8f087969eaeb5eea349d64f6857f97356592c3464b9c3ecabcc9e5feec07630a`,
and experiment script
`6674fa59e44fead9d41fb887e0634d8c363f816d1d2cceaf7886007db22d55fa`.
The delivery contained no README, checksum ledger, environment pin, captured
run output, or generated `figures/` inputs.

The bundled experiment requires Python 3.10 or later with `mpmath`, `numpy`,
`sympy`, and `matplotlib`. From this directory, regenerate the report inputs
and evidence tables with:

```sh
python3 fabius_frontier_experiments.py --output figures
```

The command writes three PNG figures, one generated TeX table, and four CSV
tables with deterministic LF line endings under `figures/`. These files are
generated evidence, not part of the three-file arrival payload.

The report's novelty screen is stale even at its pinned snapshot
`fc4b8868fcf57cc534d22f438d940ec65ebbe767`: `Frontier_Compilations` Part V
already contains the matching Laguerre--Pólya, PF-infinity, and shifted-Jensen
layer, while zero-count and sign material appears elsewhere in that volume.
The report therefore remains standalone pending a claim-by-claim crosswalk and
deliberate deduplication; paper theorem labels do not imply Lean status.

The source selects Libertinus and uses the repository's A4, 27 mm geometry.
The normalized report was rebuilt on 2026-08-31 with exactly three strict
`pdflatex` passes from the 1,060-line build source having SHA-256
`2cc6c6843478663828377456c5bc2290786ff090ad3bd0eede8a2df777a59204`;
the retained PDF is 24 pages with SHA-256
`94a4ce8adada4c32513ad95e00a64e556020f6c9fef422274cfd6ace2eef6234`.
Its log has no errors,
unresolved cross-references, rerun request, overfull box, or underfull box;
all 19 PDF font rows are embedded and subset, four are Libertinus, and no Type
3 font remains. Every page rendered and contained extractable text.

The current live TeX is 1,060 lines and 58,362 bytes with SHA-256
`e7f05ac66a92284e82886bfe8b3376715ca0f71493a217d5a1adab6c17171475`.
It now uses the shared `\TwoAdicValuation` command and postdates the render;
therefore the PDF is a retained validated checkpoint, not a rendering of the
current source. The former 12-entry payload ledger inventoried the source,
retained PDF, script, README, three PNG figures, generated TeX table, and four
CSV evidence tables at its checkpoint. It is now retired and recoverable from
Git history. The exact
five-theorem `BaseDigitMultiplicity.lean` crosswalk closes the finite
general-base digit count only; analytic zero order, product convergence, and
the sign law remain paper-level claims.
