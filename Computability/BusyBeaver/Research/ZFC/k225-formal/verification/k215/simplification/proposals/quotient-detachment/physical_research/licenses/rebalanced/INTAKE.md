# Intake note: K215-R41: rebalanced source addresses, maximum depth 41

Source archive `ZFC_K215_Rebalanced_2026-10-21.zip`, arrival commit `fddedc979d`; pinned ProveIt commit `7571649843`.

Placed in batch 202 as delivered: every staged file is byte-identical to the archive (checksum
lists, logs and TeX auxiliaries stay out by the root ignore rules). Nothing was rerun or reviewed at
intake; the claims below are the delivery's. The delivery README is `README.md`. The complete
archive is recoverable with `git show fddedc979d:docs/incoming/ZFC_K215_Rebalanced_2026-10-21.zip > ZFC_K215_Rebalanced_2026-10-21.zip`.

**Why this machine was kept.** Batch 202 discarded versions that are essentially duplicates and
preserved unique alternatives. Its table is not a state renaming of any 215-state table in the
repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), its
source differs from every placed alternative's, and it re-encodes 4,120 source addresses (19 native rows) so that the maximum address depth falls from 47 to 41 and the address sum by 6.9%, with a new source bisimulation and complete runtime, keeping K215's 95,714-step startup. Its encoding differs from `alternatives/reencoded`, which re-encodes for a counter-1 seed instead.

**Omitted members** (in the archive only): `baseline/` (copies of K215, commands120 and composed tables and the upstream exposition). A delivered verifier that reads an omitted
member needs the archive.
