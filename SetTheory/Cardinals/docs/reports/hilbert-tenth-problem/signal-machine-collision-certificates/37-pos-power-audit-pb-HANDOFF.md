# Frozen independent reduced POWER audit handoff

The mathematical verdict is **PASS with the pinned Pell theorem dependency**. Read `AUDIT.md`; its root-accepted bytes have not changed. This dossier is the immutable copy boundary for Report 67. All files are mode 0444 and all directories mode 0555. No further edits should be made here; any continuation should use a separate directory.

## Exact key pins

| File | SHA-256 |
|---|---|
| `AUDIT.md` | `411b260f35201bff1f3b6e5b761bf35ed3c8784e2f7f195573034afbd1016458` |
| `check_independent.py` | `f3fc466222a01943ddcd653ff02da0cb20e8ba32090a43ed511db4ebd696f6fa` |
| `evidence/results.json` | `c9f1df99184dac44a51f6067947f0ab013cfcd9315aef97ce6406c5b399d6d5d` |
| `replay-input/positive-power22-reduction-20261004/MANIFEST.json` | `3b75e574e694d988a05d10ddd5bde752e666b4ccac70704662111c54b1473a86` |
| `replay-input/positive-power22-reduction-20261004/SOURCE_PINS.json` | `977fe7d7a67d05d35d790ba2ecd55f5414693084c7adce7e0e973be24e1a7c37` |
| `replay-input/positive-power22-reduction-20261004/dependencies/pell-source.lean` | `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a` |

The Lean source is pinned to mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, file `Mathlib/NumberTheory/PellMatiyasevic.lean`, and is retained with its license and notice. It was read as text, not executed or rebuilt.

## Complete evidence and replay boundary

`CANONICAL_MANIFEST.json` hashes every other regular file in this dossier, including this handoff, the independent proof/checker, all eight independent full polynomial expansions, receipts, preservation snapshots, the manifest verifier, and the complete inert replay-input packet. Its only self-exclusion is itself; the externally reported manifest digest pins that file. The canonical JSON encoding is UTF-8, sorted keys, compact separators, and one trailing newline. The manifest also declares the complete directory set and final read-only modes.

The complete replay-input packet is copied byte-for-byte from the audited frozen source. Only permissions of the copy were changed to make this dossier read-only. The original source was not modified; the original before/after preservation snapshots remain included. The exact archived original author script is inert input and must not be run for this audit.

Verify the packaged dossier:

    python3 verify_manifest.py

Replay the independent scientific checks to an output path outside this dossier:

    python3 check_independent.py --source replay-input/positive-power22-reduction-20261004 --out /path/to/new-evidence

Python 3.9+ and its standard library suffice. No third-party package, network access, prior workspace path, machine interpreter, simulator, author scientific script, or Lean build is needed. Prior receipt paths are historical provenance only; replay uses the explicit source/output arguments.

Packaging did not rerun the scientific checks. The existing successful evidence covers 8 expansions, 31 elimination identities, 192 complete module evaluations, 96 reconstruction round trips, 37 symbolic infinite-family identities, and 28 composed examples. The counts are 49/38, 37/26, 33/22, and 31/20. Fixed-base degrees are 12,12,16,16; the 13-leaf variable-base degree is 20. All nonempty complete fibers are infinite. No global optimality, finite-fold, or unbounded-horizon single-polynomial claim is made.
