# Review of recent K215 proof-simplification commits

## Current-status refresh: production adoption at 0359ebda60

The latest reviewed production cutoff is `0359ebda60aaf52758358e1450a04988136db67e`, containing adoption commit `de9fdb0873b36d049d075a5c0568f2dfcff28e7a`. **Ordinary 2,240-entry certificates are now production**, through arbitrary-decoder `RMBisim.WithDecoder`, with 512-step decoding. The normalized 1,426-entry lane and final CM215 ZFC adapter remain unintegrated proposals. The recorded primary closure is 184 modules, 37 fresh plus 147 reused, with two typed clients and ten standard-axiom reports. An outer tool exit 143 after COMPLETE/PASS has unknown cause; selected compilers and both clients are recorded exit zero. This review did not rerun proof tools.

See [the full phase5 refresh and applicability matrix](phase5_refresh/PHASE5_REFRESH.md) and `phase5_refresh/STATIC_AUDIT.json`. Preserve current RMBisim and reuse its decoder/segment infrastructure for the remaining normalization-aware relation, rather than adding a second ordinary RMPlainCodec or replacing current proof modules. The follow-up's frozen experiments retain their beaabc source pin; exact runtime/calibration blobs and unchanged program/WF definitions establish targeted applicability, not a new compiled result.

**Historical review below:** all uses of “current” in sections 1–7 refer to the original beaabc cutoff. The no-production-change conclusion remains true through the placement-only 62f0f95 extension, but is superseded for later production status by this refresh.

Reviewed interval: `557b6aac99b836a8ab61fb210ba9d59061586202` through `beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc`.
Repository: VladimirReshetnikov/ProveIt. Review date: 21 October 2026.

## Bottom line

The newly placed packets contain real advances beyond the earlier Python/static prototypes: a recorded kernel-checked **1,426-entry ordinary Lean source equivalence**, a recorded compiled **ordinary one-forward-certificate Rocq source equivalence**, and several recorded compiled **exact CM215-to-production-K215 bridges**. They have not changed the production proof closure in this interval.

These are recorded compiler/kernel results whose source bindings were independently checked here, not new compilation performed by this review. No Lean or Rocq toolchain was available, no incoming executable was run, and nothing was edited or pushed in the repository.

## 1. Placement is not production adoption

The interval has six commits. The mathematical material was placed by `35ba151c3bd6289161e0c1eee864ac4328e611a0` (six packets, batch 205) and `69e6d97fc2ea6da87b718109b1c8614a0927a621` (revised packet, batch 206). Both commit messages explicitly say the intake did not rerun the contents. The other commits are archive arrivals and a merge. The final `beaabc8e3b` adds the previously delivered ZIP; it is not another mathematical result. The parent review separately bound that archive to the sealed local delivery.

The ordinary compare response stops at 300 files and is insufficient evidence for a whole-repository non-change claim. Instead, exact directory/tree objects were compared:

- Entire `Computability/BusyBeaver/Lean`: unchanged tree `5fc0e3508dc6b54ce04aa34879b3f39f970dbfaa`.
- `k225-formal/rocq`: unchanged tree `8fe465a96478fec7e60b7e0292380adc7d5d3551`.
- All top-level `k225-formal` generators, Lean subtrees, and other Rocq subtrees: unchanged.
- Only its `verification` subtree changed.

Thus neither primary Lean nor primary Rocq production closure was reduced by these commits. See `production_tree_comparison.json` and the [placed proposal index](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/README.md).

## 2. Strongest new source-certificate result: normalized Lean lane

The unnumbered `k215-simplification/source_normalization` packet is stronger in checkpoint reduction than the `-2/plain_source` packet. Its [kernel receipt](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification/source_normalization/kernel_receipt.json) records:

- Lean 4.32.0; 22 local modules and eight upstream dependencies, 30 total.
- All **1,426 entries**, 1,425 decrement entries plus one halt, and **2,851 branch obligations including entry** checked.
- Exact public `KSource215.p215_halts_iff`, universally quantified over the register file.
- Generic checker assumptions `[propext, Quot.sound]`; concrete source theorem assumptions `[propext, Classical.choice, Quot.sound]`.
- An incremental isolated successful build, not a measured clean end-to-end build. The 625.114-second sum is per-process recorded work and must not be called clean-build elapsed time.

Every one of its 22 shipped local Lean files matches the source SHA-256 of its successful receipt entry. The current production declarations `tH`, `tB`, `tC`, `p215Nodes`, `p215`, and `pathDagPerm` agree with the replacement program module after whitespace normalization.

This is not merely deleting rows from the old checker. [RMNormalizedBisim](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification/source_normalization/RMNormalizedBisim.lean) proves `tsite_ipeq` and uses a certificate relation saturated under implicit trailing-zero equality. The branch test uses `ibeq`, while increment/break operations still use the consumed leaf path returned by `tsite`. It then reuses the existing ordinary `RMBisim.Bisim.halts_iff`, so signed offsets and a separately computed reverse direction are absent. The exact binding and public facade are in [KSource215Normalized](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification/source_normalization/normalized_lean/KSource215Normalized.lean) and [KSource215](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification/source_normalization/normalized_lean/KSource215.lean).

The summary's `kernel_checked: false` belongs to the Python generator. The separate kernel receipt's true value belongs to the Lean checks. These are different scopes, not evidence of a failed kernel proof.

## 3. The ordinary 2,240-entry lane is also genuine, but not a second quotient

The [plain-source result](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/plain_source/result.json) records 70 compiled modules and the exact theorem

`Halts KSource215.p215 ⟨[], R⟩ ↔ RMDag.IterHalts DagPerm.dagPerm R`.

All 70 shipped source hashes match its ledger, and static import traversal finds no missing project module and no offset-checker import. This includes the exact tree bindings, well-formedness layer and iterative-DAG bridge, not just a generic checker theorem.

Its [decoder-parametric checker](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/plain_source/BusyBeaver/ZFC/RMPlainCodec.lean) removes the 128-bit cap by `totalDecode n := decodeAux n n []`; the packet records 622 path occurrences above 128 bits, maximum 176. The normalized lane uses a sufficient 512-step decoder. An unmodified 128-step decoder is not a valid migration.

Do not rank by archive suffix or a single size metric:

- Normalized: 1,426 entries; 30 recorded modules; 402,486 UTF-8 source bytes.
- Plain: 2,240 entries; 70 recorded modules; 346,638 UTF-8 source bytes.

The normalized tree binding uses many local bottom-up proof declarations; the plain lane factors its data differently. These counts are audited whole recorded source closures, not proof-object sizes, memory comparisons, or measured overall speedups. The normalized lane is the stronger semantic-check compression, but it is not uniformly smaller in textual source.

## 4. Important stale-dependency trap: preserve the newer production RMBisim

Seven of the normalized lane's eight upstream dependency hashes are still identical to current production. `RMBisim.lean` is not.

Current production already proves `seg_hn` by composing `seg_run` with the generic `hn_after` prefix-removal lemma. Both new packets retain the older direct induction for `seg_hn`. The exact diff is saved as `production_RMBisim_proof_delta.patch`. The change adds `atHalt_step` and `hn_after` and replaces only that proof; definitions and the `seg_hn` statement are unchanged.

Therefore integration should keep the current production [RMBisim](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMBisim.lean) rather than overwriting it with a packet copy. This is not a newly introduced mathematical gap, but a fresh replay against current imports is still necessary. The compiler receipts are for the old pinned proof module, not the current one.

## 5. Rocq: distinguish generic symmetry from actual source instantiation

Two independently useful packet results are present:

1. `k215-simplification-2/coq` has [actual offset-checker symmetry](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/coq/OffsetMirror.v) and [exact compact/original certificate equality](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/coq/CertificateIdentity.v). Its [receipt](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/coq/verification/kernel-result.json) reports Coq 8.18.0 / OCaml 4.14.1 and successful recursive `coqchk` of CertificateIdentity and OffsetMirror, closed under the global context. This packet supplies a forward-only Source215 patch, but does not itself record the patched production endpoint build.

2. `zfc215-simplification/source_proof` goes further: [Source215Simple](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/zfc215-simplification/source_proof/Source215Simple.v) actually compiles the ordinary one-direction check and `forall R, rm_halts p215 ([], R) ↔ rm_halts dagPerm ([], R)`. Its [final receipt](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/zfc215-simplification/source_proof/verification/result.json) records exit 0 and two closed-assumption reports for that module. The copied Prog215 and DagPerm are byte-identical to current production inputs. Compact data plus codec occupy 173,003 bytes versus 1,499,170 bytes for the original literal source certificate, an 88.4601% source-size reduction.

The latter receipt recursively checks exact certificate equality and the generic OffsetMirror result. **It does not record a completed separate recursive source-closure audit**: final `recursive_source_check` is `not requested`. A historical optional recursive source check was terminated, not logically rejected and not passed. Do not conflate ordinary successful compiler kernel checking with an additional completed `coqchk` audit.

Both packets used Coq 8.18, not the production Rocq 9.1 toolchain. The ordinary lane's private compatibility module supplies proved library aliases/lemma; its Rocq 9.1 branch was not executed. Full production Correct215/CorrectDense215 rebuilding and endpoint assumption reports remain gates. The current production [Source215](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Source215.v) still computes both offset directions.

## 6. CM215 already reaches the exact production machine interface

The new exact-machine bridge is not merely standalone native-table equivalence. [CM215Core](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/formal_cm215/CM215Core.lean) declares:

`BlankHalts machineCM215 ↔ BlankHalts KDense215.machine215`.

Its finite compatibility decisions cover the actual dense machine rows, and its five new proof-module source hashes match the [compiled summary](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/formal_cm215/verification/compile-summary.json). The native theorem quantifies every initial tape/head from control 0; it is not an arbitrary-control theorem without the invariant. Final dense transfer axioms are recorded as `[propext, Quot.sound]`.

The [ZFC adapter](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/formal_cm215/CM215ZFCAdapter.lean) is literally transitivity with the unchanged production [KEndpoint215](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean) theorem, followed by `not_congr`. The intermediary is exactly the same `BlankHalts KDense215.machine215`, not a similarly named duplicate table.

Thus no further mathematical lemma is visibly missing for this composition. Remaining work is build integration: make the new modules available, prefer original production imports over vendored duplicates, compile after the complete KEndpoint215 dependency closure, and inspect final axioms. The final adapter is explicitly uncompiled in the packet.

The unnumbered `k215-simplification/cm215/CM215RepoBridge.lean` independently records the same attachment through literal equality of all 430 parent rows and a compiled parameterized `inherit_calibration` theorem. `k215-transport` also has recorded compiled dense/Core attachment. These are alternative implementations, not three additive reductions. None is a new 214-state machine.

## 7. Updated priorities after this review

1. **Integrate the 1,426-entry normalized Lean lane**, retaining the current RMBisim proof refactor, exact public facade, maintained generators and existing consumers. Rebuild both typed endpoint clients and compare axioms. This closes a previous formalization gap rather than rediscovering the Python quotient.
2. **Use the existing Coq source proof**, with a small mirror-only change as the conservative first integration step if desired. Replay under pinned Rocq, then evaluate ordinary compact-data adoption and full endpoint audits.
3. **Port the now-existing normalized Lean proof to Rocq** for a genuine further reduction from 2,240 to 1,426 rows there. Required ingredients are observation congruence, zero-padding comparator soundness, and saturated relation soundness. A smaller emitted data file alone does not prove the port.
4. **Finish a single CM215 endpoint adapter build**, not another standalone simulation proof. Current exact interfaces already align.
5. Longer-term source simplification remains the certificate-free canonical effect-CFG theorem or contextual arithmetic subroutine contracts. The new packets do not supply those proofs. The 1,423-class experiment only removes three more graph classes and was already in the previous report; do not present it as a newly found state reduction. The cedge/cv dependency cut from K230.Prog230 is also already proposed in the incoming packet, not an original new finding of this review.

## Audit artifacts and limits

- `SOURCE_PINS.json`: 155 exact source paths, commit pins, Git blob hashes, verified URLs.
- `STATIC_AUDIT.json`: independent static checks, all 155 local Git blobs matching; 22 normalized and 70 plain-source receipt bindings; selected CM215/Coq bindings; current production dependency comparisons.
- `verify_receipts.py`: this review's own static audit; it reads data only and never imports incoming scripts.
- `commits.json`, `packet_tree.json`, `production_tree_comparison.json`: provenance.
- `sources/`: exact read-only snapshots obtained through the GitHub connector.

This review did not reproduce object hashes, execute any incoming checker, run a proof assistant, establish a full-build performance improvement, or modify any earlier research/release/delivery artifact.
