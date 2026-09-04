# Reproducibility assets

This directory is the canonical, deduplicated home of the numerical and
symbolic supplements used by the inverse-Fabius synthesis.  Its subdirectories
are named by mathematical role rather than by the names of the five source
packages:

- `inverse-germs/` contains finite-prefix inverse-germ and Richardson checks;
- `self-sampling/` contains exact tables, Appell data, the complete rational
  Sturm certificate for `A_8`, and sampling figures;
- `endpoint/` contains the all-orders, Wright--omega, and exact dyadic-tail
  experiment lanes;
- `computability/` contains the standard-library finite-spline and modulus
  check;
- `inverse-iterates/` contains the inverse formal-reversion diagnostic;
- `provenance/` preserves immutable arrival ledgers and corpus audits.

The root-level `ASSET_DISPOSITION.csv`
records the SHA-256, size, semantic class, destination, and disposition of all
88 files in the two superseded source subgroups. Package checksum manifests are
retired. Reproduce and validate the migration record with:

```text
python -B ../audit/build_asset_manifest.py --check
```

## Python environment

The source packages supplied lower bounds rather than a fully pinned lock.
`requirements.txt` is their deduplicated union, using the strongest supplied
lower bound for each dependency.  The computability script uses only the
Python standard library.

## Publication-safe figure variants

The original Matplotlib PDF figures are retained as immutable reproducibility
assets, but their embedded math text uses Type-3 glyphs.  The canonical master
therefore includes the corresponding high-resolution PNG variants.  Three
were supplied by the source packages.  The two dyadic-completion variants were
rasterized from their single-page PDFs at 300 dpi with Poppler:

```text
pdftoppm -png -r 300 -singlefile \
  endpoint/dyadic-completion/figures/psi_periodic.pdf \
  endpoint/dyadic-completion/figures/psi_periodic
pdftoppm -png -r 300 -singlefile \
  endpoint/dyadic-completion/figures/dyadic_tail_convergence.pdf \
  endpoint/dyadic-completion/figures/dyadic_tail_convergence
```

Their migration receipts are recorded in `ASSET_DISPOSITION.csv`. This changes
only the publication container: the plotted data and visual content remain
those of the retained vector originals.

```text
python -m pip install -r requirements.txt
```

Run experiments into a separate `reproduced/` directory; do not overwrite the
reviewed snapshots in place.  The following commands are issued from this
`assets/` directory:

```text
python self-sampling/scripts/experiments.py \
  --output reproduced/self-sampling

python inverse-germs/scripts/generate_data.py \
  --output-dir reproduced/inverse-germs
python inverse-germs/scripts/verify_symbolic_fast.py \
  > reproduced/inverse-germs/symbolic_fast.txt

python endpoint/all-orders/scripts/inverse_fabius_asymptotics.py \
  --output-dir reproduced/endpoint/all-orders \
  --precision 100 --modes 12 --depths 5 10 20 40 80 120 160

python endpoint/wright-omega/scripts/inverse_fabius_experiments.py \
  --output-dir reproduced/endpoint/wright-omega \
  --dps 100 --modes 9 --symbolic-order 3

python endpoint/dyadic-completion/scripts/inverse_fabius_experiments.py \
  --output-dir reproduced/endpoint/dyadic-completion \
  --max-saddle-order 3

python computability/inverse_fabius_computability_experiments.py \
  > reproduced/computability.txt

python inverse-iterates/numerical_experiments.py \
  --output-dir reproduced/inverse-iterates \
  --x0 0.437123456789 --iterate-count 4 --max-order 22
```

The inverse-iterate program also regenerates three forward-iterate plots that
are byte-identical to assets already owned by the corrected forward-iterate
report under `drafts/representations/`; those duplicate payloads are
deliberately not copied here.  Its forward Taylor-root plot also remains out
of the canonical asset set pending reconciliation with that corrected report.
No numerical output is a premise of a theorem.
