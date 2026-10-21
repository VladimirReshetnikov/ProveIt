# Intake note: Re-encoded K215 with a counter-1 seed (K215_Alternative_Encodings, primary)

Source archive `K215_Alternative_Encodings_2026-10-21.zip`, arrival commit `cd59611687`; pinned ProveIt commit `7de71bd17b` (batch 199's write).

Placed in batch 201 as delivered: every staged file is byte-identical to the archive (checksum
lists stay out by the root ignore rules). Nothing was rerun or reviewed at intake; the claims below
are the delivery's. The delivery README is `README.md`. The complete archive is recoverable with
`git show cd59611687:docs/incoming/K215_Alternative_Encodings_2026-10-21.zip > K215_Alternative_Encodings_2026-10-21.zip`.

**Why this machine was kept.** Batch 201 kept only materially distinct 215-state implementations
(Vladimir's direction, 21 October 2026). Its table is not a state renaming of any table already in
the repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), and
its design differs: the source keeps K215's 202 nodes and 4,751 primitives but re-encodes 4,519 instruction addresses, and the blank bootstrap changes (716,307 steps to a zero-PC root with the counter at 1, calibrated in `proof/seed_calibration.md`).

**Omitted members** (in the archive only): `parent/` (the earlier K215_Composed_Commands_Selector archive), the `published11_134` tables in `provenance/` (copies of `alternatives/composed`), and `secondary/`: the packet's secondary machine changes only the rho6 sampler, whose semantic source is intake 199's (Source 163), so it is not materially distinct. A delivered verifier that reads an omitted
member needs the archive.
