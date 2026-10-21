# Production refresh at 0359ebda60aaf52758358e1450a04988136db67e

## Result

Production adoption is now real. Commit `de9fdb0873b36d049d075a5c0568f2dfcff28e7a`, included at this cutoff, replaces K215's zero-offset certificate representation with **2,240 ordinary four-field entries** and uses arbitrary-decoder soundness in `RMBisim.WithDecoder`. It does **not** adopt the normalized 1,426-entry quotient or the final CM215 ZFC adapter. The historical no-production-change findings through `beaabc8e3b` and `62f0f95e2b` remain correct for their intervals, but are not the current status.

The complete comparison from 62f0f95 to 0359 has 246 files, below GitHub's 300-file comparison cap. It changes 25 production source/generator files: RMBisim, RMEquiv, ConstructibleAbs, InternalSat, 18 generated KSource215 outputs and three generators. No production Rocq file changes. Exact paths and patches are in `COMPARISON.json`. Current ZFC Git tree: `ad7a2ec5ca3373068f8a68917b41eb037b0cd0dc`.

## Evidence checked, and its limits

The recorded primary Lean closure has 184 modules: 37 fresh and 147 reused with recorded source, dependency, object and log bindings. Two typed clients yield ten axiom reports, all using only the standard Lean axioms. There are 31 project linter warnings and zero audit warnings. All 16 source-certificate chunks are recorded fresh; 18 generated outputs are bound. Separately, 15 fresh legacy modules and five interface checks extend the union to 199 modules. This is not a clean all-199-module rebuild.

The outer tool session reported **exit 143 after the driver's COMPLETE/PASS output**. Its cause is explicitly not established. The observation records all selected compilers and both clients exiting zero, and independent live/saved binding checks accepted the kernel records. Do not describe the outer shell as successful or the event as a kernel failure. The exact observation, independent review and publication finalization are preserved in `evidence/lean/`.

Our own static checker verifies 42 fetched Git blobs and SHA-256 hashes, both current typed-client result entries and their ten reported axiom sets, the independent-review hash, and the published result summary hash. Distinguish the original execution result digest `97df8504afb8bcb9a2bc4efe4bb033eeebc977e4da452a03036923cd7424bcea` referenced by live/saved/outer records from the published augmented summary digest `c3c87c23b3ee5723ae9b970fbacb514a3cbb4f4b9e362e33235bbce4dc79bf0c`, which matches the downloaded result and finalization. These are different documented artifacts, not a hash failure.

We did not reopen all archived 184-module logs or objects, execute the archive's validators, run incoming code, or run Lean/Rocq. Compiler and object-rehash results remain recorded evidence, not independent compiler reruns here.

## Exact adoption and remaining normalization delta

KSource215Data falls from 456,548 to 432,131 bytes. Static parsing verifies every one of 2,240 old five-field entries becomes precisely the same four-field entry after removing its zero offset. `decode215 n := decodeAux 512 n []` is retained. There are 622 entries with at least one path longer than 128 bits; the source migration cannot use the legacy decoder unchanged. The complete program, tree and WF section and the public `p215_halts_iff` proposition are unchanged.

Production's new `WithDecoder` soundness needs no decoder injectivity or numeric bound. A second ordinary `RMPlainCodec` is therefore redundant. Keep the current RMBisim, including its newer `seg_run`/`hn_after` proof, rather than overwriting it with a vendored packet copy.

The remaining normalized lane is a small semantic extension, not another decoder implementation: reuse production `CTree`, `lookupC`, `allC`, `WithDecoder.getc decode215`, `seg` and its soundness infrastructure, and `Bisim.halts_iff`. Add the packet's zero-padding comparator `ibeq` and soundness, `tsite_ipeq` observation congruence, a relation saturated under `RMEquiv.ipeq`, normalized branch/entry tests and their soundness bridge. Keep increment/break updates on the consumed path returned by `tsite`. Ordinary `WithDecoder.Rel` and literal `lbeq` do not already validate the alias quotient. Rebuild the 1,426-entry certificate and exact facade against these current imports; the old receipt is not that replay.

Other adopted proof reductions are genuine: RMEquiv.fwd's main induction shrinks 83 to 61 lines without statement or surrounding-source changes; InternalSat removes repeated impossible-tag cases through private inversion helpers, 1,433 to 1,321 lines; ConstructibleAbs shares private bounded-quantifier transport, 997 to 992 lines. The semantic receipt's current source hashes match the fetched files.

## Applicability matrix for this follow-up's frozen experiments

All finite experiments remain pinned to `beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc`; no frozen input or output was rewritten.

| Topic | Current input evidence | Consequence |
|---|---|---|
| Runtime | KTable215, KRuntimeCore, KSim, KZip, RegisterPathClean and SiteCoverage retain exact Git blobs. KSource215Data is not byte-identical as a whole, but its entire 258,134-character program/WF/tree section is byte-identical. | Literal machine and runtime interfaces used by the home-return/decoder work remain applicable. No new kernel compilation is implied. |
| WF | DagPerm, DagDom and L2RootPerm retain exact blobs. RMEquiv's prefix, fwd statement and suffix are byte-identical; only fwd's proof changes. KSource215Data's tH/tB/tC, WF checker/proof, program arrays, trees and path bridge are identical. The generator changes certificate rendering, not its WF table computation. All other pinned proposal/WF inputs are absent from the complete changed-file set. | Rank/scope summaries still address the same data and WF obligations. Update an integration patch's imports/layout for the adopted ordinary checker, not the frozen experiment. |
| Calibration | All 15 pinned production files, including Code254GIC, KSeedModel222, KLowerQHyp, KLowerSeed and the intermediate chain, retain exact current ZFC tree blobs. Both pinned structural-proposal files are unchanged. | The calculus derivability-interface opportunity is not subsumed by phase5. Changes to imported ConstructibleAbs/InternalSat proofs do not change these inspected interfaces, but a future formal integration still needs rebuilding. |
| Terminal contract | The pinned k215-transport/formal/PositiveStutter.lean is absent from the complete changed-file set. | The proposed terminal-field weakening remains an uncompiled proposal. Phase5 neither adopts nor invalidates it. |

Machine-readable per-file old/current blobs are in `STATIC_AUDIT.json`. `SOURCE_PINS.json` uses portable relative `local` paths and includes Git blobs, SHA-256, bytes and verified pinned URLs. Replay only the review-authored `verify_phase5.py`; its output is `STATIC_AUDIT.json`.

## Decoder-sharing novelty check

The newly committed decoder-sharing research note is a finite 281-class dispatcher census and proposes whole-tape local-frame contracts. It explicitly measures no return-sharing count and introduces no new checker or compiled proof. It neither derives the follow-up's 234-to-180 guarded-role factoring nor proves its home scanner. The 281 incoming traces must still be credited as prior input; the later factoring is a narrower interface/result, not a complete runtime proof or demonstrated kernel speedup. The exact note is preserved as `evidence/decoder-sharing-notes.md`.

## Sources

- [Production adoption commit](https://github.com/VladimirReshetnikov/ProveIt/commit/de9fdb0873b36d049d075a5c0568f2dfcff28e7a).
- [Phase5 overview at the review cutoff](https://github.com/VladimirReshetnikov/ProveIt/blob/0359ebda60aaf52758358e1450a04988136db67e/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase5/README.md).
- [Outer execution observation](https://github.com/VladimirReshetnikov/ProveIt/blob/0359ebda60aaf52758358e1450a04988136db67e/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase5/lean/outer-execution-observation.json).
- [Current generic checker](https://github.com/VladimirReshetnikov/ProveIt/blob/0359ebda60aaf52758358e1450a04988136db67e/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMBisim.lean).
