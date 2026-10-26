# B1/B2 late novelty screen

Frozen source/corpus pin: `09d65a93c9df8684c1a226341d6a5120623d1cdb` (observed 2026-10-26, 18:01:35 UTC), 22 commits after `e652d21c413de59e4821f6e8e9b6a3a077bf5bfe`. No later commits are included.

## Decision

- **B1: exclude from new recommendations.** [Packet w report, lines 480–507](https://github.com/VladimirReshetnikov/ProveIt/blob/09d65a93c9df8684c1a226341d6a5120623d1cdb/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/report.tex#L480-L507) explicitly constructs temporal shared-edge grids with finite cyclic successors, names reset→initializer matching, and targets the existing TraceCycle initialization/finish/last-row proof. [EdgeFieldsCore, lines 47–60](https://github.com/VladimirReshetnikov/ProveIt/blob/09d65a93c9df8684c1a226341d6a5120623d1cdb/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/lean/EdgeFieldsCore.lean#L47-L60) gives `grid_temporal := rfl`. Although B1's local patch is not textually the same, it has no demonstrated residual benefit when this prior architecture is assumed applied. Do not count its four source lines.
- **B2: retain narrowly.** One actual halted color/head split and one `Fin 2` bit witness jointly construct `Allowed.pass` and `Allowed.finish`. Prior fibers and later canonical-row/receiver arguments are extraction/classification results, not this paired forward construction. Packet w [explicitly leaves literal allowedness](https://github.com/VladimirReshetnikov/ProveIt/blob/09d65a93c9df8684c1a226341d6a5120623d1cdb/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/report.tex#L503-L507) and [finite-table membership](https://github.com/VladimirReshetnikov/ProveIt/blob/09d65a93c9df8684c1a226341d6a5120623d1cdb/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/report.tex#L577-L583) as remaining work. Complete source delta:164 → 155 physical lines, −9, with helper and wrappers charged. Uncompiled.

## Freshness and coverage

All a–u directory Git tree hashes equal the earlier audited pin. New v is the inherited six-proposal Round3 packet; its README was re-read. New w's complete report and edge-grid core were read. All four incoming ZIPs were inspected as source data: Post_Adoption; further-deltas; proof-refinements; structural-simplifications. Exact Git blob identities, source locations and SHA256s are in the JSON receipt.

Both current target files were fetched at the closing pin and compared byte-for-byte to the packaged source. TraceCycle Git blob: `f475e11cff4f3168f97020d6d1c7f6aa5bc15447`; FinishConstruction: `708b6f76c087f87abcac9ec96ae750ba9fb44cdc`. Both are unchanged. The compare metadata is corroborative only; unchanged claims do not rely on a possibly capped compare list.

No Lean execution, installation, imported script execution, repository mutation, or performance measurement was performed. The prior virtual baseline was not physically merged. These are mechanism-level novelty findings with exact source freshness, not kernel validation.
