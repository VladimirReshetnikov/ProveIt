# Latest-main targeted recheck

Pinned latest main: `e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`.
Fetched through the connected GitHub reader, 2026-10-21 18:22–18:24 UTC.

## Important change

Reverse source-certificate elimination is **already implemented** at this revision:

- `RMOffsetBisim.lean` now adds `delta_neg`, `OBranchGood.symm`, `OBisim.symm`, and `ocheck_halts_iff`.
- `KSource215.lean` imports only the sixteen forward check modules and obtains its public halting equivalence from `ocheck_halts_iff`.
- `KSource215Data.lean` drops all backward-certificate definitions and retains the exact same 2,240 forward entries. Every offset is zero. Maximum pointer lengths remain 45 and 176 bits. The existing 512-iteration decoder remains unchanged.
- Source-data size is now 456,548 bytes, down from 653,569 bytes in the historical pinned snapshot. Small header changes account for the difference between this delta and the isolated former backward-section size.

The report's original zero-offset projection proposal is therefore superseded by upstream's stronger signed-offset symmetry. Do not describe it as new unfinished work or suggest adding the prototype redundantly.

Source links:
- [Forward-only public theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215.lean)
- [Signed-offset symmetry](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMOffsetBisim.lean)
- [Forward-only data](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean)

## Proposals that remain new

All nine `KSites215Batch000`–`008` headers were rechecked at the latest pin and still import `BusyBeaver.ZFC.KSource215`, not `KSource215Data`. Their returned Git blob hashes match the historical pinned copies. The import-only patch remains applicable to the batches; retaining the facade's former transitive interface is still recommended.

A further targeted read of phase-three/phase-four sources established that compact coverage assembly is already implemented: the facade is now 14,916 bytes / 235 lines and directly composes the same105 checked blocks. `DomRho8` is now30,114 bytes /517 lines, AX7,563/161, and EnumPerm22,788/545. Generic successful-prefix cancellation and shared enumerator command execution are also implemented. These supersede the earlier report's corresponding proposals and sizes. Canonical-site certificates, balanced lookup for site runtime checks, import narrowing, context-aware sharing and Core-level positive-stuttering transport remain separate proposals. See `profiling/README.md` and `latest_phase4_status.json`.

## Verification boundary

No Lean compiler ran in this investigation. The newly read published phase-four receipt explicitly records185 modules:10 freshly compiled and175 predecessor objects hash-bound, with both typed clients and ten standard-axiom reports. This is an attributed incremental kernel-check receipt, not a build independently performed here and not a fresh full replay. Historical timings remain attached to the original 613f9cf28 full-build receipts read at b6fb232, not to latest main. `latest_status.json` records the checked files and outcomes.

The separate portable `verify_snapshot.py` reproduces the historical zero-offset/mirror/path-length and import audits using only the packaged snapshot. It passed under normal Python and was actually tested to reject `python -O`. Its output is source verification, not a proof-assistant result.
