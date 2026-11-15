# Provenance and changes

The frozen original ORH inputs and `vendor/engine_foldscreen.py` come from
Vladimir Reshetnikov's ProveIt repository, commit
`7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`, in
`docs/incoming/PA194ORH_research_2026-11-15.zip`, archive root
`PA194ORH_research/`. The inputs are from `machines/PA194ORH/`; the engine is from
`research/engine/engine_foldscreen.py`.

The shared compiler, support utilities, and symbolic executor reside at
`../../construction/vendor/` and retain their original comments. They are
byte-identical to the same paths under `construction/vendor/` in the ORH archive.
See the package's `licenses/` directory and main provenance material for upstream
license and attribution information. `PROVENANCE.json` freezes the dependency
hashes, so the imports can be checked without an external checkout.

The joint-forest and ORH search scripts were developed during this research
session. For this portable copy, only input/import/output paths and optional
`--output` arguments were changed. The tree enumeration, matching, mutation,
validation, and search-order algorithms are unchanged. The original script
hashes are recorded in `PROVENANCE.json`.

Reference machine tables, run summaries, individual receipts, and logs were
copied from the completed searches. In the novelty record only table paths were
made relative to `reference/`; its comparison results were preserved. The
portability verification record documents the short reruns performed after
relocation.
