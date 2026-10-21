# Intake note: NIP/MP/DROP command order with zero-valued spares (K215_Zero_Spare_Command_Compositions, primary z201)

Source archive `K215_Zero_Spare_Command_Compositions_2026-10-21.zip`, arrival commit `7571649843`; pinned ProveIt commit not stated (its parents are pinned in its own files).

Placed in batch 200 as delivered: every staged file is byte-identical to the archive (checksum
lists stay out by the root ignore rules). Nothing was rerun or reviewed at intake; the claims below
are the delivery's. The delivery README is `README.md`. The complete archive is recoverable with
`git show 7571649843:docs/incoming/K215_Zero_Spare_Command_Compositions_2026-10-21.zip > K215_Zero_Spare_Command_Compositions_2026-10-21.zip`.

**Why this machine was kept.** Batch 200 kept only materially distinct 215-state implementations
(Vladimir's direction, 21 October 2026). Its table is not a state renaming of any table already in
the repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), and
its design differs: the command order NIP/MP/DROP (command family 201) combined with the zero-spare backend, and a new safe startup (570,263 steps; the earlier unsafe frame is cleaned by NIP, NIP, DROP, MP(1)).

**Omitted members** (in the archive only): `secondary/` (byte-identical to `alternatives/zero-spare-transfer`'s machine) and `primary/inherited/{baseline,machine,research}` (copies of K215, of the Z215 delivery and its command-family research, including this table's reconstruction base); `primary/inherited/licenses/` is kept. A delivered verifier that reads an omitted
member needs the archive.
