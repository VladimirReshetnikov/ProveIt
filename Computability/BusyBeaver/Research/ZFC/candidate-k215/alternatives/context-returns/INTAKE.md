# Intake note: History-dependent returns, and a shallower K215 decoder

Source archive `ZFC_K215_Context_Transfers_2026-10-21.zip`, arrival commit `b6fb232916`; pinned ProveIt commit `7571649843`.

Placed in batch 204 as delivered: every staged file is byte-identical to the archive (checksum
lists, logs and TeX auxiliaries stay out by the root ignore rules). Nothing was rerun or reviewed at
intake; the claims below are the delivery's. The complete archive is recoverable with
`git show b6fb232916:docs/incoming/ZFC_K215_Context_Transfers_2026-10-21.zip > ZFC_K215_Context_Transfers_2026-10-21.zip`.

**Why this machine was kept.** Batch 204 discarded versions that are essentially duplicates and
preserved unique alternatives. Its table is not a state renaming of any 215-state table in the
repository or elsewhere in the batch (rooted breadth-first canonical form; intake check), and
it supplies two machines: `k215-context` (K215's source with five history-dependent return rewrites in the decoder) and the principal `k215-shallow` (the same returns on a source reassociated in three closed blocks, 1,042 addresses changed, maximum depth 46). It also proves a 201-subtree three-command transfer/cache enumerator at source level.

**Omitted members** (in the archive only): `upstream/` (copies of the pinned K215). A delivered verifier that reads an omitted
member needs the archive.
