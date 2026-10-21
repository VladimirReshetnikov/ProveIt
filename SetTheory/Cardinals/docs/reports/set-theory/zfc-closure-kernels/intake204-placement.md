# Batch 204 placement: proof simplification and GC–ZC215

Source 167 continues this report's numerical-calculus/machine correctness programme and its exact K215 proof work. The archive arrived as `docs/incoming/Proof_Simplification_and_GC-ZC215_2026-10-21.zip` in commit `05d063acef885d47be5a2ce6645b046f98f7ea02`; its Git blob is `6efc60b3963e1eabba1bc129a0edab42b66c4bb5`. The next tracked local prefix was167. Existing 165/166 payloads and their untracked follow-up records are untouched.

The [complete map](data/intake204-placement.json) accounts for all 82 delivered files: 61 new exact-byte ancillaries,14 existing exact copies, 4 repeated members mapped to another placement, and 3 archive-only files (the main README, manuscript and PDF). New delivered files total 5,111,957 bytes; the longest path is 123 characters. The nested SB correction ZIP is kept intact with its [18-member inventory](data/intake204-nested-correction.json). Files are renamed with `167-proofgc-` and short component labels; code belongs in `code/`, data in `data/`, and explanatory Markdown beside this note. Original relative filenames inside delivered files remain unchanged. The map is the authority for every rename and duplicate.

This is a placement record, not a new execution or proof acceptance. The manuscript, full hybrid compiler/proof comparison, occurrence-injection argument, inherited calibration and SB correction were read. No supplied program, checksum manifest, Lean/Rocq compiler or binary runtime was executed. All82 extraction members were compared with the immutable arrival bytes by Git blob identity; all 79 non-archive-only members match their mapped file. Git history was inspected before deduplication. There was no line-ending normalization.

The proof proposal is pinned to older commit `c9dc79323429112c698100f3226a6e4d56c8b782`. Its symmetry recommendation has already been implemented and checked in the maintained phase-two K215 proof; its historical compilation totals are not a new benchmark. Delivered prototypes remain uncompiled delivery evidence. The useful four-field zero-offset certificate/generic 512-decoder proposal is separately under investigation; the ordinary 128 decoder cannot replace the512 decoder for the 622 longer-path pairs. Placement adopts no proof patch and leaves the current formal endpoint status unchanged. The [reference comparison](data/intake204-pinned-references.json) records the exact pinned matches and extra terminal LF bytes without changing either source.

The hybrid GC–ZC215 and nested SB215 correction are retained as distinct research. Reported 6,177-case runtime and 117,004-step startup results are submitted evidence, not fresh intake replays. The correction rejects both SB215 variants for a wrong source return and explicitly leaves FT215 unaffected. A written reconciliation will follow separately under the overlapping-delivery rule; it will also distinguish total formula decoding from noncanonical codes and reconcile stale prospective passages with the delivery's later completed hybrid argument.

Only this one arrival ZIP is retired in this placement. Other incoming archives remain pending; this does not clear the queue.

To recover the exact 82-file layout in a new directory, from the repository root run:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake204.py --repo . --out /tmp/recovered-source167
```

The [recovery helper](code/recover-intake204.py) reads the placed files and immutable arrival Git object and checks Git blob identities. It neither verifies a delivered checksum manifest nor executes delivered code. The submitted top-level verifier includes a manifest suite and is not an approved intake command; any later fresh tests must be selected separately and run on a disposable recovered copy.
