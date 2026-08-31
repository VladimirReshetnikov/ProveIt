# Shape, divisibility, and Stein geometry of the Fabius--Rvachev law

This directory preserves and normalizes the report received on 2026-08-30 in
`Fabius_Rvachev_Frontier_Report_2026-08-30-C.zip` (outer SHA-256
`200e65588b824d05f863ec0dae50b983408af3a7a2cf000c55556560e8e49d2e`).
All 14 submitted payload checksums verified before repository normalization.
The original 50-page Letter/Latin-Modern rendering and its four Type-3 vector
plots remain recorded in repository history. The current vector companions were
regenerated with embedded, subset fonts and contain no Type 3 fonts.

## Corrected corpus and proof-status boundary

The submitted novelty audit was incomplete. It missed the already-filed
`Fabius_Stein_Koopman_Frontier_Report/`, present at repository ancestor
`31549ad44`. That sibling already proves the exact scalar Stein-kernel formula,
dyadic rationality and special values, Appell/Bell moment identities, and a
stronger two-term Lambert-periodic endpoint law.

Accordingly, those kernel and endpoint strands are overlapping independent
manuscript derivations, not repository-distinct results. The strict
log-concavity, identical-convolution rootlessness, invariant diffusion, and
Legendre formal-jet strands remain distinct under the corrected audit checkpoint
`563b90f25e0563cc521a53e9b478b667eaf3b694`. A theorem label means that this
manuscript supplies a paper proof under its stated inputs; it does not assert an
exact Lean counterpart.

The imported nowhere-analyticity input does already have exact Lean counterparts:
`Fabius.rvachev_not_analyticAt` in
`FabiusFunction.OriginalPaperSupplement` and
`Fabius.canonical_rvachev_not_analyticAt` in
`FabiusFunction.NowhereAnalytic`. The report now crosswalks those existing inputs
separately from its Shape/Stein theorem and conjecture labels. All suggested
Shape/Stein declaration names are prospective API names only; none of the new
paper results is claimed to have an exact Lean counterpart.

## Maintained files

- `Fabius_Rvachev_Shape_Divisibility_Stein_Geometry.tex` is the canonical
  A4/Libertinus article source.
- `Fabius_Rvachev_Shape_Divisibility_Stein_Geometry.pdf` is its required
  same-stem generated artifact.
- `rvachev_frontier_experiments.py` deterministically writes LF-normalized CSV
  and text output plus four metadata-stable PNG figures.
- `numerical_output/*.png` are the raster companions embedded by the normalized
  TeX source.
- `numerical_output/*.pdf` are normalized vector companions retained for
  high-resolution inspection; all fonts are embedded and subset, with no Type 3.
- `requirements.txt` records minimum top-level dependency versions, not a full
  environment lock.
- `SHA256SUMS.txt` is the package ledger and must be refreshed only after the
  normalized three-pass PDF build and final payload freeze.

## Numerical reproduction

The numerical program uses no network or random input. From this directory:

```bash
python3 -m pip install -r requirements.txt
python3 rvachev_frontier_experiments.py --output-dir numerical_output
```

The defaults use 200001 grid points and 24 fixed-point iterations. The script
checks probability mass, symmetry, `up(0)=1`, `up(1/2)=1/2`,
`tau(0)=5/36`, `tau(1/2)=1/12`, and
`E[tau(Z)]=Var(Z)=1/9`. Byte-for-byte floating-point and Matplotlib replay still
requires a fixed complete Python environment; the submitted package did not
record one.

The checked-in PNG companions were first produced from the preserved vector
figures at 180 dpi with Poppler:

```bash
for stem in up_density score_monotonicity stein_kernel endpoint_stein_ratio; do
  pdftocairo -singlefile -png -r 180 "numerical_output/$stem.pdf" "numerical_output/$stem"
done
```

Future script runs write the selected PNG format directly and leave the submitted
vector PDFs untouched.

## PDF build

After the numerical inputs exist, run exactly three serial passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Shape_Divisibility_Stein_Geometry.tex
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Shape_Divisibility_Stein_Geometry.tex
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Shape_Divisibility_Stein_Geometry.tex
```

Then verify A4 geometry, embedded/subset Libertinus prose fonts, zero Type-3
fonts, resolved references, page count, rendered pages, and the refreshed live
ledger before committing.

The normalized artifact was rebuilt with those exact three passes on
2026-08-30. It has 34 A4 pages; all 20 font entries are embedded and subset,
seven are Libertinus, and none is Type 3. The final log has no overfull box,
TeX error, unresolved reference, or rerun request. The title/status page,
corrected corpus boundary and Lean-input table, overlapping Stein identities,
all four embedded PNG figures, endpoint-status correction, suggested-name section, and final page
were rendered and inspected. Build sidecars were removed, and the exhaustive
18-entry live ledger was refreshed only after this final payload freeze.
