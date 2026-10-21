# Intake note: Transfer-pop with append-zero spares (Zero_Spare_Transfer_215_and_Alternatives, primary)

Source archive `Zero_Spare_Transfer_215_and_Alternatives_2026-10-21.zip`, arrival commit `7571649843`; pinned ProveIt commit `cd59611687`.

Placed in batch 200 as delivered: every staged file is byte-identical to the archive (checksum
lists stay out by the root ignore rules). Nothing was rerun or reviewed at intake; the claims below
are the delivery's. The delivery README is `README.md`. The complete archive is recoverable with
`git show 7571649843:docs/incoming/Zero_Spare_Transfer_215_and_Alternatives_2026-10-21.zip > Zero_Spare_Transfer_215_and_Alternatives_2026-10-21.zip`.

**Why this machine was kept.** Batch 200 kept only materially distinct 215-state implementations
(Vladimir's direction, 21 October 2026). Its table is not a state renaming of any table already in
the repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), and
its design differs: the three-command transfer-pop source (Source 166's language) with the append-zero spare policy and a newly proved protected blank startup (73,172 steps).

**Omitted members** (in the archive only): `secondary_association/` and `optional_reparse/` (re-associations of this source with identical guarded successors and effects, so not materially distinct), `mp0_216/` (216 states), `supplement/` (comparisons, negative controls, supporting results), and the copies of K215 and of the transfer215 parent in `primary/inputs/`. A delivered verifier that reads an omitted
member needs the archive.
