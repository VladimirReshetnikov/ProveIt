# Intake note: ZC215: zero-credit enumeration

Source archive `ZC215_Research_2026-10-21.zip`, arrival commit `a10b2c302c`; pinned ProveIt commit `29e2cc4c55`.

Placed in batch 204 as delivered: every staged file is byte-identical to the archive (checksum
lists, logs and TeX auxiliaries stay out by the root ignore rules). Nothing was rerun or reviewed at
intake; the claims below are the delivery's. The complete archive is recoverable with
`git show a10b2c302c:docs/incoming/ZC215_Research_2026-10-21.zip > ZC215_Research_2026-10-21.zip`.

**Why this machine was kept.** Batch 204 discarded versions that are essentially duplicates and
preserved unique alternatives. Its table is not a state renaming of any 215-state table in the
repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), and
it reorders the tags to DROP 0 / NIP 1 on `alternatives/commands120` and enumerates raw candidates 0, 1, 2, ...; replacing a NIP by DROP lowers a candidate, which injects every NIP of a prefix into an earlier DROP, so the scheduler needs no AX stack credit (`proofs/tag_lowering_credit.md`). Native start 74, rows 8/1 and 198/0 change.

**Omitted members** (in the archive only): `reference/` (copies of commands120 and of the K215 exposition). A delivered verifier that reads an omitted
member needs the archive.
