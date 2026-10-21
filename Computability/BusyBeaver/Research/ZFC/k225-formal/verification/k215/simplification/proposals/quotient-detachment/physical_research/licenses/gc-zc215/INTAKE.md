# Intake note: GC-ZC215: command-tag generalization with zero-credit enumeration

Source archive `Proof_Simplification_and_GC-ZC215_2026-10-21.zip`, arrival commit `05d063acef`; pinned ProveIt commit `c9dc793234`.

Placed in batch 204 as delivered: every staged file is byte-identical to the archive (checksum
lists, logs and TeX auxiliaries stay out by the root ignore rules). Nothing was rerun or reviewed at
intake; the claims below are the delivery's. The complete archive is recoverable with
`git show 05d063acef:docs/incoming/Proof_Simplification_and_GC-ZC215_2026-10-21.zip > Proof_Simplification_and_GC-ZC215_2026-10-21.zip`.

**Why this machine was kept.** Batch 204 discarded versions that are essentially duplicates and
preserved unique alternatives. Its table is not a state renaming of any 215-state table in the
repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), and
it composes `alternatives/gc215` with `alternatives/zero-credit` (`hybrid215/machine.native.tm`, start 74), with its own runtime and a 117,004-step blank-to-root check; `prefix_credit/` abstracts ZC215's credit argument as an uncompiled Rocq lemma. `correction/` holds the review that refutes both SB215 machines (batch-204 queue entry).

**Omitted members** (in the archive only): `proof_refactor/` (placed separately as `k225-formal/verification/k215/simplification/proposal-2026-10-21/`), `hybrid215/zc215.reference.*` (copies of ZC215) and `hybrid215/unmerged216.reference.tm` (an inert 216-state allocation). A delivered verifier that reads an omitted
member needs the archive.
