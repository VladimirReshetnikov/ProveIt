# Intake note: Transfer enumeration with MP first (T215_Transfer)

Source archive `T215_Transfer_2026-10-20.zip`, arrival commit `7571649843`; pinned ProveIt commit `ead95b5b33`.

Placed in batch 200 as delivered: every staged file is byte-identical to the archive (checksum
lists stay out by the root ignore rules). Nothing was rerun or reviewed at intake; the claims below
are the delivery's. The delivery README is `README.md`. The complete archive is recoverable with
`git show 7571649843:docs/incoming/T215_Transfer_2026-10-20.zip > T215_Transfer_2026-10-20.zip`.

**Why this machine was kept.** Batch 200 kept only materially distinct 215-state implementations
(Vladimir's direction, 21 October 2026). Its table is not a state renaming of any table already in
the repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), and
its design differs: the transfer machine's command tags are reordered to MP = 0, S = 1, AX >= 2 (two closed bodies exchanged, eight rows changed), with a new one-head stack-credit bound from candidate cutoff 1. `MP0_Transfer_215.zip` (same drop) delivers a state renaming of this same table and was not placed.

**Omitted members** (in the archive only): `reference/` (copies of the accepted K215 and the transfer parent) and `research/`. A delivered verifier that reads an omitted
member needs the archive.
