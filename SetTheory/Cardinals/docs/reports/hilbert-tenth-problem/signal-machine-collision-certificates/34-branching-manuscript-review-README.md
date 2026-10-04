# Report 64 manuscript review dossier

Read `AUDIT.md` for the accepted final verdict and its scope. Acceptance applies only to the exact final candidate-d PDF and source pins in `FINAL_BINDING.json`.

## Evidence files

- `transcription_check.py`: fresh inspected static transcription checker; never imports scientific sources
- `static_results.json` and `static_execution.log`: its retained final run and exact input-file identity
- `frozen_sources_before.json`, `frozen_sources_after.json`: byte/mode/nanosecond-mtime preservation comparison
- `FINAL_BINDING.json`: independently authenticated PDF, standalone source, modular pin map and flattening result
- `SOURCE_BINDING.json`: independent eleven-module flattening and cross-reference checks
- `REPLAY_BOUNDARY_CHECKS.json`: six expected rejections of unsafe or reused replay output paths
- `PAGE_INVENTORY.json`: SHA-256, dimensions and visual-review disposition for every final rendered page
- `pages/`: independent final-page PNGs at 140 dpi, generated directly from the final pinned PDF
- `Report64-extracted.txt`: text extraction used as a secondary check, not a substitute for visual inspection
- `render.log`, `pdfinfo.txt`: rendering and PDF metadata evidence
- `DOSSIER_MANIFEST.json`: final inventory of the dossier except the inventory file itself

The preliminary candidate b was not accepted. Its misplaced figure annotations and sparse final page were corrected by the author before the final exact-byte review. The final inventory must not be interpreted as applying to candidate b.

## Read-only replay

Inspect the checker first. It requires explicit absolute nonsymlink paths and a new external output directory. It rejects overlap with the release, either scientific source tree, or the checker tree, and refuses an existing output directory. Do not redirect any command over a release file.

From an extracted release root, substitute absolute paths:

    python3 -I -S -B manuscript-review/transcription_check.py \
      --release "$PWD" \
      --physical-source "$PWD/science/frozen-proof" \
      --arithmetic-source "$PWD/science/arithmetic" \
      --prior-physical-snapshot "$PWD/audits/physical/source-inventory-before.json" \
      --prior-arithmetic-snapshot "$PWD/audits/arithmetic/source_snapshot_before.json" \
      --output-dir /tmp/report64-manuscript-replay-new

Preservation comparisons use the original snapshots and therefore require metadata-preserving extraction. A normal unzip may preserve bytes without preserving the nanosecond modification times.

Rendering is a separate ordinary PDF operation. In another fresh external directory:

    pdftoppm -r 140 -png /absolute/path/to/Report64.pdf /tmp/review-render-new/page
    pdftotext -layout /absolute/path/to/Report64.pdf /tmp/review-render-new/extracted.txt

Replay outcomes are new supporting evidence. The mathematical argument is in the report and the independent scientific audits, and visual acceptance additionally requires inspecting every newly rendered page. Static check counts, physical audit counts and arithmetic audit counts are not additive theorem counts.
