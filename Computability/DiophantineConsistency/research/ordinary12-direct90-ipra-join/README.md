# Guarded 90 iPRA join preparation

No join has been run and no iPRA endpoint is claimed by this directory.

`adapter-preflight.py` analyzes the captured selected serialized headers for all project imports of the three proposed generic adapter modules. `observations/adapter-preflight01/result.json` pins the exact input inventory, corrected 425-source cone, source bytes and historical object headers. It finds that `IPRAExpressionNative` and `HAExpressionAssembly` lie inside that cone. `IPRAStandardTheory` has 263 ancestors in the cone and four affected dependents outside it, which must be rebuilt in this serialized/source dependency order:

1. `DiophantineConsistency.IPRASuccessorInduction`
2. `DiophantineConsistency.IPRAAddOneGeneral`
3. `DiophantineConsistency.IPRASuccessorInductionConverse`
4. `DiophantineConsistency.IPRAStandardTheory`

`IPRAReferenceInductionConversion` has no 425-cone ancestor in the retained header graph; that is an observation about the captured graph, not a substitute for checking actual finalized headers. Its 38 selected-project ancestors and eight outside names are recorded in the result. The prior direct-model import preflight separately identifies 65 direct selected objects absent from the provisional canonical provider. The completed cone, source corrections, all selected overlaps and companions, and any newly discovered adapter dependencies must be rechecked after the worker stops.

A join must use freshly compiled copies of the four affected modules and the three generic adapters ahead of the canonical provider. It must not select the historical four affected objects. The direct-model objects absent from the canonical provider may be supplied only after the final manifest and their full actual serialized closure have been reconciled. An actual final transitive header scan must include the rebuilt adapters, reference conversion, the direct halt root, and the client, detect any additional affected dependents and duplicate namespaced bindings, and record first-resolved object/companion paths. Preserve all attempts and do not conflate this selected-provider audit with package, dynamic, or complete source-object ancestry.

`run.py` is the initial unlaunched runner retained for the audit record. `run-v2.py` is a revised, still unlaunched runner: it requires the exact terminal stage-425 receipt and final overlay digest, accepts the final corrected cone by path and digest, revalidates all 425 source pins and matching producer receipts/guards/logs, reconciles selected missing modules, scans actual project headers, rebuilds the four affected modules and three adapters in a fresh root, and checks the endpoint's six axiom reports. It resolves package and Lean-sysroot imports explicitly, rejects unresolved names, and guards directly selected package/sysroot objects and companions. The runner and its plan require independent audit before execution. Its intended result still excludes package-transitive, dynamic, and complete historical source-object ancestry.

`run-v3.py` retains v2 and adds exact per-stage dependency-list/companion guard coverage plus end-of-run receipt-input checks. It currently rejects every source path/hash change from the pinned stage317 cone, including any future stage419 correction, until a separately reviewed exact replacement is pinned in a new runner. It remains unlaunched and under independent review.

`run-v4.py` retains v3 and additionally snapshots every newly built object and companion, binds the supplied completion receipt to the validated stage-425 producer, and refuses package/sysroot fallback for every known project-module name. It remains unlaunched. The worker's exact final cone and completion receipt, the finalized overlay manifest, and completion of the independent runner audit are required before use.

The v6 attempt failed at its first rebuild because Lean selected a partially populated namespace directory; see `ATTEMPT01.md`. `run-v7.py` is an unlaunched repair that creates one fresh project union, adds the 65 audited supplemental modules, and replaces only fresh symlinks for the four affected standard modules before rebuilding. It snapshots and rechecks the complete fresh union and each new object's companions. An independent v7 audit and a fresh attempt are required before any endpoint claim.

The v7 attempt compiled the first four stages but was correctly rejected by the strict warning policy at stage 04; see `ATTEMPT02.md`. A source-pinned exact three-warning baseline and mutation tests have been prepared. `run-v8.py` integrates only that exception and remains unlaunched; `run-v9.py` additionally rechecks copied stage sources throughout and rejects tagged as well as untagged Lean diagnostics. V9 is unlaunched and under independent review.
