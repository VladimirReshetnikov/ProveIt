# Final independent package review

Reviewed the final `verify_all.py`, README, construction builder, independent literal verifier, clock inspector, novelty checker, new mathematical report, and existing release receipt. The package is `output/pa194_joint_forest_research` at ProveIt pin `7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`.

## Findings

No substantive mathematical defect or reproduction/security blocker was identified. The source count is **3,671 instructions**, of which **1,107 are decrements**. Two branches for each decrement give **4,778 outcomes**: **4,777 nonhalting endpoints and one halt endpoint**. The affine duration envelope and its accumulated polynomial agree: `698+18*k` sums to `9*k*k+689*k`.

The relative proof correctly assigns zero duration to the absorbed source halt. It uses the lower bound only when the source is still live, and reflects a physical halt at time `t` to a source halt by `t+1`. This avoids an invalid global positive-duration assumption. The written absolute conclusion openly inherits the revised AX11H calibration; finite Python receipts are not described as an end-to-end arithmetic or Lean proof.

The existing release receipt accurately records reuse of previously checked, hash-bound literal contracts and recomputation of novelty. It must not be relabeled as a fresh literal replay. The default wrapper branch invokes the independent interpreter on the parent and all three rebuilt children; the reuse branch instead copies the delivered child certificates and checks their exact table/contract hashes and source/clock closure. Frozen metadata is additionally protected by the release manifest once sealed.

## Small fixes made with authorization

- Added `macro_bindings.json`, `local.json`, and `receipt.json` to the exact rebuild comparison. The wrapper now compares all twelve deterministic builder outputs, matching its documentation.
- Added an optional `--output` receipt path, retaining the previous default, so independent reviews can preserve the supplied release receipt.
- Clarified the 3,671/4,778 counts in README.
- Clarified that the additional ForestX fold joins runtime control41 to the two-increment reader99, which is also shared with AX; **both controls belong to the fixed budget**, rather than the66 AX-counted reader budget.

No report source was edited. The previously noted theorem/equation cross-reference was reported to the author for correction.

## Portability and execution scope

The release entry point resolves its inputs relative to its own package, runs Python through an argument vector with `shell=False`, and has no network or original-checkout requirement. Its writes are confined to a temporary rebuilt tree and the chosen replay receipt. The optional full-census rerun separately requires the documented pinned Git repository. Standard-library imports and local attributed modules suffice for the main construction and finite verification. Running Python with assertions disabled is explicitly rejected by the release wrapper.

The manifest was not yet present at the start of this review because the author was still finalizing package contents; it should be generated after the authorized README/wrapper edits. The fast wrapper replay with all548 reference forms recomputed passed in11.49seconds. Its receipt is `inventory/final_review_fast_replay.json`. The default fresh full literal wrapper replay also passed, in298.77seconds, including the AX11H parent and all three children (**19,112 source outcomes** in total). The immutable result is included as `verification/fresh_literal_replay.json`; the mutable default `verification/release_check.json` is initially the same successful fresh result. The fast replay is retained separately as `verification/construction_novelty_check.json`.

All three children reproduce the delivered independent contract and receipt bytes exactly. Every source/clock metric and novelty result agrees between the two replay modes. The parent's inherited contract file has five fields per outcome (`site`, `positive`, `duration`, `motion`, `symbolic_steps`); the current checker additionally emits rows, event-kind counts, and traces, and uses a new receipt schema/family name. The parent's regenerated contract and receipt therefore have different hashes, while its source/clock metrics and literal table hashes agree. No byte-identity claim is made for those two parent certificate representations. The fresh run establishes their current literal-machine checks directly.

This review verified both wrapper branches, with all548 reference canonical forms recomputed in each. It found no remaining blocker. The complete release manifest still needs to be sealed by the author after these final review files are copied.
