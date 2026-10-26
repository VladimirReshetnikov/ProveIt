# Round 6: exact source and recent history

## Scope and reproducibility

- Repository: `VladimirReshetnikov/ProveIt`.
- Research source pin: `9d9d1123b39927d30363f1dcd53c23f0575c30ee` (26 October 2026, 19:00:19 UTC).
- Commit root tree: `27cd4a2601eb2dc7b491f1dd4cf298b0779338b9`.
- Active Lean subtree: `c4eb5bb585fbc61b1951466d7804ec000e3f1007`.
- `sources/`: all **702** blobs in the complete active Lean subtree, plus **8** pinned configuration/context files. The complete recursive tree has 704 entries, including directories; `truncated=false`.
- `dependencies/`: **27** selected files: all direct external repository imports of the active subtree, plus `SignInvariantPolynomial`. This is not a transitive dependency closure.
- `comparison_sources/`: **14** old-file copies, seven each at the round-5 source and closing pins. These establish exact changed-file line counts, not aggregate simplification savings.
- `provenance/review_sources/`: **12** exact repository review documents. Compiler observations in them belong to their original authors, not this source-only session.
- Root toolchain: `leanprover/lean4:v4.32.0`. No Lean invocation, installation, Lake build, repository write, or upstream mutation was performed.

Run `python provenance/verify_snapshot.py` from this packet. It performs offline Git-tree reconstruction, ancestor-edge binding, Git-blob SHA-1 and SHA256 checks of bundled files, full active-source coverage, both tree deltas, both commit-set checks, proposal inventory checks, and the closing candidate equality check. Incoming ZIP bytes are intentionally not bundled: default mode binds their saved Git blob IDs to the trees and records saved SHA256 values, explicitly **without replaying their byte hashes**. `archive_verification_receipt.json` records the earlier full local-byte check. If the seven immutable archives are separately materialized at their manifest paths, add `--with-archives` to require their byte replay; missing archive bytes then fail. It does **not** elaborate proofs. The selected snapshot is not a complete Lake checkout.

## Exact comparisons

| Baseline | Ahead commits | Added active files | Modified | Removed |
|---|---:|---:|---:|---:|
| Round-5 source `e1c8914bc7064d9a8e7c06171a18069a949badd0` | 27 | 12 | 7 | 0 |
| Round-5 closing `91dce223cda86c0755b8a9b2504f84be04443fce` | 17 | 10 | 7 | 0 |

The active file counts come from complete recursive Git trees, **not** capped GitHub compare file arrays. Commit sets are corroborated against the pinned 100-commit parent graph. See `active_tree_delta.json`, `since_closing_delta.json`, `commit_timeline.json`, and `since_closing_commit_timeline.json`.

## Already adopted simplifications, not round-6 discoveries

| Commit | Module | Old → new physical lines | Net removed | Change |
|---|---|---:|---:|---|
| `57a5eed4d8` | `RefinedPair` | 83 → 86 | −3 | Formal polynomial identity replaces chosen complex roots. |
| `f1949d7be7` | `NativePellPower` | 180 → 163 | 17 | Reuse ordinary lower-ratio estimate. |
| `f3b6ad87d0` | `NativePellStepDown` | 230 → 210 | 20 | Reuse odd-index divisibility criterion. |
| `4fc484d4c8` | `RegisterNatPairing` | 160 → 148 | 12 | Reuse pair-existence certificates. |
| `afbec38df7` | `NativeCyclicRotation` | 176 → 159 | 17 | Derive rotation through single-impulse convolution. |
| `8274c8f6b2` | `SelectiveCarry` | 194 → 176 | 18 | Prove degree bounds first, then coefficient vanishing. |
| **Total** | **6 modules** | **1023 → 942** | **81** | Includes the three-line cost in `RefinedPair`. |

Exact old/current bytes independently reproduce this 81-line figure. The repository's adoption and review records report unchanged old public axiom reports and independent exact-source reviews; this session did not rerun those compiler checks. The recorded cumulative 3097-line series total is historical repository evidence, not a new measured saving claimed here.

## Newly added mathematical work, not simplification savings

- `c09a185954`: `CurrentControllerSubsets2011` and checks, constructing actual Boolean power subsets for controller targets.
- `4eb790b50c`: `CurrentControllerPositions2011`, `CurrentDummySafety2011`, and checks, supplying physical positions and ordinary nonwrapping bounds.
- `fda0ca33d3`: `NativePackingPopulation`, `CurrentWordRephase2011`, and checks, deriving exact mask population and preserving the same packing across whole periods.
- `493d46d498`: `CurrentPackingRank2011` and checks, binding the constructed rank to exact population and a strict growth bound.

The seventh modified active file is the aggregate import module. New results and their checks must not be counted as negative simplification savings.

## One bounded closing screen

Main was observed **once** at `451b548a198c791e81abc40435979c89edb40b23`. All closing reads were pinned to that commit; no later main polling was performed. This does not replace the source pin.

- `CurrentPackingRank2011.lean` remains whole-file identical: Git blob `d71fff2ced7817e3d3278bbdb3724a48f9e2e22a`. See `CLOSING_target_binding.json` and the closing ancestor trees.
- Research inventory grew from 36 to 41 packet directories, adding `zk` through `zo`; all five complete new packet trees are retained.
- At source pin, incoming held five ZIPs and README. All five ZIP bytes are Git-blob/SHA256 verified.
- At closing, incoming held two new controller ZIPs and changed README. Those bytes and changed research README/ADOPTION are also verified. Semantic novelty review belongs to `baseline_audit/`, separately from this source record.

## Acquisition and delivery

GitHub connector reads acquired all new text sources and tree metadata. Previously captured source bytes were reused only after exact Git-blob verification. Public immutable raw URLs were used for ZIPs after the connector rejected binary content as non-UTF-8; this was a format limitation, not an access denial. One optional whole-repository recursive-tree request failed with `Transport closed`; it was not used. All relevant subtrees were acquired complete and verified independently.

`curated_delivery_manifest.json` selects the portable evidence files. It omits huge raw HEAD/compare/history responses, temporary pending lists and acquisition scratch files, retaining compact immutable commit bindings and all evidence required by the default offline verifier. Raw incoming ZIP bytes are excluded; no expected source/dependency file is optional.
