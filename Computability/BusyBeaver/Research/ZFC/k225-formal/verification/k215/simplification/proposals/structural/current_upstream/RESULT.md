# Targeted proof-simplification upstream refresh

Current main: **05d063acef885d47be5a2ce6645b046f98f7ea02**, twelve commits after c9dc79323429112c698100f3226a6e4d56c8b782. Inspected read-only on2026-10-21. No received code was executed and no fresh Lean compilation was performed.

## Already integrated

Generic offset-bisimulation symmetry is now maintained in `RMOffsetBisim.lean`: `OBranchGood.symm`, `OBisim.symm`, and the one-certificate `ocheck_halts_iff`. `KSource215.lean` imports only16 forward check modules and invokes that theorem; the16 backward modules and mirrored data are removed. Therefore removing the2240 reversed checks is not a new proposal against this main.

This is more than a source-only change. The saved run2 Lean4.32.0 record has exit0, input hashes unchanged, duration0.365321853seconds, and an output object hash. Its raw compiler log reports `OBisim.symm` and `ocheck_halts_iff` depend only on propext and Quot.sound. The run3 facade check is retained separately. These are upstream recorded checks, not fresh local checks. The phase4 adoption receipt additionally reports PASS_ADOPTED_AND_CHECKED for the185-module primary closure,10 freshly compiled modules and175 reused hash-bound predecessor objects, two typed endpoint clients and ten standard axiom reports. It is an incremental audit, not a fresh build of all185 modules.

## Still applicable proposals

- **All-zero-offset specialization:** current data still contains2240 forward OTree records, every offset literally0; the facade still uses the generic offset checker.
- **Canonical ordinal graph replacing the pair certificate:** p215Nodes, p215, t215, tD, fwd0 through fwd15, and fwdCert are text-identical to the saved c9 declarations. Thus the graph proposal's source inputs and2240 rows have not changed. The proposed1426 vertices/814 aliases are not independently recomputed here; this refresh establishes that its pinned input remains current.
- **Two-lookbehind decoder-template product:** KRuntimeCore, KSim, and SiteCoverage are unchanged. KSites215 has a shorter join facade, but still certifies4751 individual source leaves in105 kernel blocks. No281-template replacement appears in the inspected maintained modules.
- **Semantic round-trip removal:** KSeedModel222 is unchanged, including enc_dec_enc and eqFree_dec_enc around lines174–200 and their subsequent use. The proposed patch is not integrated.

The saved connector copies of the four unchanged modules each contain one extra terminal newline relative to the raw current files. `UNCHANGED_MODULES.json` records the byte difference and equality after terminal-newline normalization rather than silently claiming byte identity.

## Sources and receipts

- Current commit: https://github.com/VladimirReshetnikov/ProveIt/commit/05d063acef885d47be5a2ce6645b046f98f7ea02
- Maintained symmetry: https://github.com/VladimirReshetnikov/ProveIt/blob/05d063acef885d47be5a2ce6645b046f98f7ea02/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMOffsetBisim.lean
- Recorded symmetry evidence: https://github.com/VladimirReshetnikov/ProveIt/tree/05d063acef885d47be5a2ce6645b046f98f7ea02/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase2/source-symmetry
- Current incremental endpoint audit: https://github.com/VladimirReshetnikov/ProveIt/tree/05d063acef885d47be5a2ce6645b046f98f7ea02/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase4

Local receipts: REFRESH_RECEIPT.json, SOURCE_COMPARISON.json, UNCHANGED_MODULES.json, symmetry_record.json, symmetry_compiler.log, symmetry_facade_record.json, symmetry_facade_compiler.log, and phase4__adoption-complete.json.

The latest commit itself adds an incoming historical proposal ZIP. Its README describes its archived symmetry draft as uncompiled. That historical status does not supersede the separately maintained and checked symmetry implementation now present in the tree. The remaining proposals above are assessed only against the inspected current source, not as global novelty claims.

## Literal formal table binding correction

The exact maintained native table is SHA2569683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2. It differs from the earlier366ae5... decoder-experiment table despite identical source17af2071.... All430 formal `KTable215.lean` rows are independently parsed and exactly equal to9683 after renaming254→230,301→102,302→120. See FORMAL_TABLE_BINDING.json and the owned check_formal_binding.py. Decoder-template measurements must therefore be refreshed on9683 before being attributed to the maintained formal machine; the runtime worker is handling that refresh. This does not change the source-graph or semantic-round-trip input comparisons.
