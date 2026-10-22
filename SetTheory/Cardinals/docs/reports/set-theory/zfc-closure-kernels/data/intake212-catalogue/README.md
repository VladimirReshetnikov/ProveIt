# Batch 212 catalogue evidence

The maintained manifest was rebuilt in two passes with shell escape disabled. [result.json](result.json) records the exact manifest, builder, commands and raw output pins. The [final review](final-review.json) checks all290 ordered rendered entries against290 tracked report directories, all fonts embedded, no TeX diagnostics, every page footer, and the changed pages2,123,141. The base article and its50labels are byte-identical to placement9740f2bd; the reconciliation-note exception introduces no article-label changes.

The catalogue extension keeps the other289 entry bodies byte-identical. The long source-archive list appends only batch212, and the placement list appends only9740f2bd13. The original manifests are recoverable from that placement commit; historical control paths point to the actual scratch run. The three maintained catalogue files are the collection README, manifest.tex and manifest.pdf. No proof source or producer was changed.

`build_catalogue.py --repo REPOSITORY --out FRESH_DIRECTORY` replays the own two-pass build for the exact pinned manifest and leaves its PDF in the new directory. The update and final-validation scripts are historical execution records with their original scratch paths. No delivered script or proof compiler was run. The three PNGs preserve the visual review surfaces.
