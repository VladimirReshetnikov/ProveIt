# Intake note: Z215: zero-valued spare blocks and a two-truth startup

Source archive `Z215_Zero_Spare_2026-10-21.zip`, arrival commit `cd59611687`; pinned ProveIt commit `3249800496`.

Placed in batch 200 as delivered: every staged file is byte-identical to the archive (checksum
lists stay out by the root ignore rules). Nothing was rerun or reviewed at intake; the claims below
are the delivery's. The delivery README is `README.md`. The complete archive is recoverable with
`git show cd59611687:docs/incoming/Z215_Zero_Spare_2026-10-21.zip > Z215_Zero_Spare_2026-10-21.zip`.

**Why this machine was kept.** Batch 200 kept only materially distinct 215-state implementations
(Vladimir's direction, 21 October 2026). Its table is not a state renaming of any table already in
the repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), and
its design differs: K215's commands with zero-valued spare blocks (row 198/0 writes 0) and a new startup from native state 74, with its own startup proof.

**Omitted members** (in the archive only): `baseline/` (a copy of the parent candidate-k215, which is in the repository) and `research/`. A delivered verifier that reads an omitted
member needs the archive.
