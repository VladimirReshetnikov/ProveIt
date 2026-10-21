# Intake note: Zero-spare allocation on the MP-first transfer machine

Source archive `K215_Zero_Spare_MP_First_2026-10-21.zip`, arrival commit `34b63b3b19`; pinned ProveIt commit `f5b2db607f`.

Placed in batch 202 as delivered: every staged file is byte-identical to the archive (checksum
lists, logs and TeX auxiliaries stay out by the root ignore rules). Nothing was rerun or reviewed at
intake; the claims below are the delivery's. The delivery README is `README.md`. The complete
archive is recoverable with `git show 34b63b3b19:docs/incoming/K215_Zero_Spare_MP_First_2026-10-21.zip > K215_Zero_Spare_MP_First_2026-10-21.zip`.

**Why this machine was kept.** Batch 202 discarded versions that are essentially duplicates and
preserved unique alternatives. Its table is not a state renaming of any 215-state table in the
repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), its
source differs from every placed alternative's, and it composes the zero-spare backend (`alternatives/zero-spare`) with the MP-first transfer language (`alternatives/mp-first-transfer`): row 198/0 writes 0, a new dirty-cache startup (73,172 steps, then a 177-step AX prefix) and a conservative-debt-one protection argument; 6,209 guarded cases.

**Omitted members** (in the archive only): `machine/parent/` (the T215_Transfer packet: the placed `alternatives/mp-first-transfer` and the research batch 201 left in its archive). A delivered verifier that reads an omitted
member needs the archive.
