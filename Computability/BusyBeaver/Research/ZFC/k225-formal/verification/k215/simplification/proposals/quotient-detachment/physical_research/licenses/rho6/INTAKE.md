# Intake note: K215-R6: the rho6 parameter permutation on both K215 command orders

Source archive `K215_Rho6_Permutations_2026-10-21.zip`, arrival commit `fddedc979d`; pinned ProveIt commit `7571649843`.

Placed in batch 202 as delivered: every staged file is byte-identical to the archive (checksum
lists, logs and TeX auxiliaries stay out by the root ignore rules). Nothing was rerun or reviewed at
intake; the claims below are the delivery's. The delivery README is `README.md`. The complete
archive is recoverable with `git show fddedc979d:docs/incoming/K215_Rho6_Permutations_2026-10-21.zip > K215_Rho6_Permutations_2026-10-21.zip`.

**Why this machine was kept.** Batch 202 discarded versions that are essentially duplicates and
preserved unique alternatives. Its table is not a state renaming of any 215-state table in the
repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), its
source differs from every placed alternative's, and it changes the source: the sixth axiom generator emits rho6(A,B) instead of rho6(A,C) (four operands, two native rows), with a repaired axiom-selection compiler and its own cofinal enumeration argument. `machines/rho6_120/` applies it to the DROP/NIP/MP order of `alternatives/commands120`, `machines/rho6_210/` to the primary K215; each has its own complete runtime and blank prefix. The permutation itself is Source 163's (at 216 states, `candidate-k216/alternatives/rho6`). Batch 201 dropped the rho6_210 table when it arrived as the unproved secondary of `K215_Alternative_Encodings`; this packet supplies its complete proof.

**Omitted members** (in the archive only): `baseline/` (copies of candidate-k215 and its commands120 and composed alternatives). A delivered verifier that reads an omitted
member needs the archive.
