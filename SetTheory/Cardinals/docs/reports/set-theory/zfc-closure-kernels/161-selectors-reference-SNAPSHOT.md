# Selected historical inputs

This directory intentionally contains selected unchanged files from two previous submissions, not both complete release trees.

`partial216/` includes exactly the inputs needed to reconstruct the partial-selector source and native table from the included K217 archive. `permuted216/` includes the source builders, numerical/source calibration article, historical source inputs, and primary permuted source needed by the top-level K215 verifier.

The preserved `permuted216/README.md` and `report.tex` describe the original full 216-state submission and may mention files omitted from this selection. Use the top-level `README.md`, `report.pdf`, and `verify.py` for the actual K215 release workflow. No claim is made that the selected historical directory is a standalone complete 216-state audit tree.

The two original archive hashes and inspected repository commit are recorded in `provenance/INPUTS.json`. The exact common K217 archive is preserved, including its nested K218 predecessor, so the new finite verification chain has its required offline inputs.

`foundational/KLower221.lean` is the exact numerical-calculus endpoint module from the pinned repository. It is included to make the cited theorem and ZF/ZFC composition directly inspectable. Its imports belong to the larger repository; this selected source file is not a standalone proof-assistant build or a K215 endpoint.
