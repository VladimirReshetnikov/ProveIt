# Reproduce the independent 245-state audit

## Required original artifact

Use the separately delivered `zfc245-proof-20261018.zip`, preserved byte-for-byte.

- ZIP SHA-256: `5a38b0e7475905584eabcb75912caa8d5f4149148e8c2a2439b2702a9de49ba1`
- Canonical table SHA-256: `17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`
- Original-label table SHA-256: `f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`
- Grammar SHA-256: `724ad366bb56206a3aac233932e6a8bfc10a49192f5a4d6689c873c5c1d6a278`

Original contribution provenance: https://chatgpt.com/c/6ad42686-bb4c-83e8-a49b-947cc7786102 . This is the user's supplied research source, not a public repository or a claim of discovery by this supplementary audit.

## Portable independent audits

Python 3.10 or later is recommended (tested with Python 3.12.14). No network, external package, theorem prover, full source checkout, or heuristic search is needed.

    python3 verify_manifest.py
    python3 run_audit245.py --archive /path/to/zfc245-proof-20261018.zip --output /path/to/fresh-audit

The output directory must not exist. The script validates the exact ZIP hash and safe extraction paths, then copies evidence into fresh scratch. Four independently written audit scripts are run without importing the new candidate's checker implementations. The universal runtime audit imports the previously reviewed baseline affine engine; its six minimal dependencies are included unchanged and hashed in source-subset-manifest.json. The independent source audit uses the previous source parser and compares five inherited proof files plus the exact logical-seed module. The encoding audit freshly reconstructs every row and parses the original Coq source.

`--only literal`, `--only source`, `--only runtime`, or `--only encoding` runs one selected audit. Results and stdout/stderr logs are under the chosen scratch output. Exit zero requires every selected command to pass.

A fresh packaged replay of all four scripts passed. The delivered log and result copy is in reproduction-evidence/audit245-independent-run/.

## Expanded original certificate replay

Add `--core` to the command above. This additionally runs the original archive's `code/verify_all.py --whole-frame` in the fresh extracted copy. The complete independent review also ran:

    python3 -B code/verify_all.py --whole-frame --literal --output /path/to/new-results

Run that command from a writable copy of the original extracted archive. The optional literal regression needs a C++17 compiler. Its observed complete run passed in 356.814 seconds: 8,391 arbitrary-value whole-frame cases, 2,312,645 symbolic rules, all 490 table rows, minimum 13 literal steps, 8,390 pointer normalizations, 8,385 regenerated finite literal fixtures, 54 bootstrap equations, 1,410 scanner contractions, and exact 407,915-step initialization. Time is host-dependent.

Final review documents and certificates are in research_sub246/verification/audit245_*. The expanded whole-frame JSON, core results, and logs are under audit245_runtime_replay/. The large generated literal-cases.txt and instruction-metadata.json are omitted from this supplement; the above command reconstructs them. The immutable original archive already contains all candidate inputs and its own frozen certificates. All 293 original delivered-file hashes were rechecked after the full audit, with no modified or unexpected file.

## Proof boundary

Finite literal tests are corroboration. Universal claims rely on literal-step, unary-run, finite-list, actual-table macro, complete-frame and source-bisimulation induction arguments, plus the inherited logical calibration. These are ordinary proofs formalizable in ZFC. No new exact-table Lean/Rocq endpoint or serialized ZFC/PA proof is supplied, and no minimality claim is made.
