# Copy-only KSource215 contingency

Use only if the active monolithic build fails or exceeds its existing cap. Discard this contingency if that run passes. No compiler was invoked and no active repository source was edited here.

`draft1/partition.json` contains the exact input hash, ordered module/file hashes, and all 32 moved theorem locations. `partition.py` is an independent text-copy authoring utility, not a Lean checker. Its only executed action was producing this scratch draft and comparing declaration tokens.

The source is partitioned into 34 modules:

1. `KSource215Data`: all original imports, literal data, 179-node source DAG, both expanded decoder trees, both complete 2,240-entry certificate data trees, WF proof and early API declarations. It contains no fwd/bwd `allO` checker proof.
2. `KSource215FwdCheck00` through `15`, and `KSource215BwdCheck00` through `15`: each imports only Data and contains exactly its original one-line `decide +kernel` theorem for 140 entries. Each independent compiler process can release that proof's elaboration/evaluation memory before the next process starts.
3. `KSource215`: same public module path and namespace, imports Data plus all 32 checked units. It retains the two start checks, the two both-child Boolean compositions, four exact-tree aliases and final `p215_halts_iff`, with every original body and statement unchanged. The final axiom print is retained.

All 90 original `def`, `abbrev`, and `theorem` declarations occur exactly once in the partition, with identical source tokens after removing comments and whitespace. The proof options remain explicitly `maxRecDepth 65536` and `maxHeartbeats 8000000` in every unit. All 4,480 individual directional entry checks and the full original 2,240-entry coverage per direction remain necessary. There are no new axioms, proof shortcuts, changed predicates, replaced certificate entries, or raised resource limits.

This changes compilation boundaries and adds 33 modules to the import closure (171→204 project modules if no other changes occur). The namespace remains `SetTheory.BusyBeaver.ZFC.KSource215`; importing the facade continues to expose the original public API. No consumer source changes should be required. A fresh dependency inventory and final axiom audit are still required after adoption. The earlier literal audit must read `p215Nodes` from Data if the facade is replaced; its historical source pin must remain preserved rather than silently relabelled as current.

The common data module still contains the original WF/rfl kernel work and large literal terms. Imported objects retain literal data, and the facade imports all proof objects. Therefore this partition is a resource-control proposal, not a guarantee that any unit or final import will fit a fixed cap. A smaller subchunk design would be a separate later change if a 140-entry proof itself is too costly.

## Generator integration proposal

The active generator first constructs a single string `out` whose declaration bodies match this draft. The narrow reproducible integration is to apply this partition after producing that string, then write the 34 results into the selected output directory. The existing original monolithic emission should be retained in history or available as an explicit option. The current scratch utility accepts `--source ORIGINAL --output FRESH_DIRECTORY`; it never imports or invokes the supplied generator and refuses to reuse an existing output directory.

Opening owns the actual adoption/build decision and may transplant the text partition into the existing generator after reviewing it. Do not install `original-KSource215.lean` as a Lean module; it is only the preserved failed/original source. Compile in the order recorded in `partition.json`, one shared-lock process at a time, then resume the existing dependent modules and both final typed audits. Preserve the original monolithic attempt and any timeout/orphan cleanup before proceeding.
