# Pinned source and novelty review

Repository: VladimirReshetnikov/ProveIt.
Current pin: cbf94cb552a3b49509e0eee80e7455d4eb5974c6.
Previous delivered-review pin: 6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95.
Inspection: 2026-10-23 UTC. This is a read-only source/integrity review, not a proof build.

## Current source baseline

The current KEndpoint215 import closure contains exactly **174 project modules, 1,752,650 UTF-8 source bytes and 37,648 physical lines**. The previous closure had **178 modules, 2,093,112 bytes and 40,517 lines**. Thus the current source closure is smaller by 4 modules, 340,462 bytes and 2,869 lines.

These are static project-source metrics. They exclude Lean's standard library, compiled objects, proof-term size, wall time and independently retained compatibility modules. The quoted changes must not be added to narrower per-file or older-phase savings.

The current snapshots were reconstructed from connector-fetched bytes and exact Git-blob matches with retained prior snapshots. Every current source byte matches the pinned Git tree; all project imports resolve. The baseline snapshots match the prior phase-14 source bindings. The standalone owned verifier recomputes current hashes, exact current snapshot membership and imports. For the baseline it recomputes the recorded graph and metric sums from a retained historical source/import ledger; the baseline bytes are not bundled. It runs no downloaded program.

The phase-15 README's 176-module count describes an earlier checked selection. It does not describe the latest maintained sources. The current closure removes Bootstrap, Code254Models, DefinableClosure, KCodeDom, KIndisc222, KSeedModel222 and PSCCalibration from the earlier closure, and adds KSeedDirect222, KSeedInterface222 and PowerSets.

## What is already integrated

1. **Relation-parametric transfinite recursion, shared quotient syntax, PowerSets boundary and dense synchronization**: adopted in phase 15, commit cd67e7badef3. Re-proposing these four ideas as new would duplicate maintained work.

2. **One quotient construction**: 8e46744a76f3 adopts the QHyp core and CP/GIC adapter. Current QuotientModel.ofCPGIC is at lines 22 onward; the Domain, quotientMember and satisfaction facades specialize KQ1Model. The maintained generate_kq1.py producer was retired. The earlier phase-15 shared-syntax arrangement is no longer the whole current implementation.

3. **Computed decoder trees**: 775267c38acd replaces tree literals with ptree applications. Current KSource215Program.lean:196 is t215 := ptree p215; KSource215Data.lean:103 is tD := ptree pathDagPerm. This is not a new remaining simplification.

4. **Direct compilation of C222**: fa92b88f8e62 adopts the Compilable-predicate interpretation in both Lean enumerators. Current EnumPerm.lean:485 and EnumDom.lean:511 construct blocks directly from C222, so KCodeDom leaves the endpoint closure. Rocq 7b4ee981be81 does the corresponding thm222 compilation and removes ThmDom from the K215 lane.

5. **Shared Rocq implication core**: 85cbbc9651d0 makes both CD222 and DomRho8 adapters of DominatedCore. Current K215 DomRho8.v is 1,009 bytes, not the formerly reviewed 22,673-byte development. The generic core is also copied into the 217, 218 and 221 generated lanes.

6. **Normalized one-sided Rocq source certificate**: 16a674f36017 replaces the 2,240-entry ordinary certificate by 1,426 normalized entries. Current Source215.v:9 checks NCheck.check once; line 12 derives the full arbitrary-register halting equivalence through check_one_sided_iff. Later 3c03a2dc937c folds the three necessary mirror helpers into NormalizedBisim and retires BisimMirror. The current 215 generated directory has 43 files.

7. **AX successor inference**: 4fb82d6f8424 adopts the local alternative of proof-boundaries. L2AxiomsPerm.lean:84 reads successor addresses from the program; its line-120 word contains macro atoms without the 156 repeated successor annotations. The two-program shared AX-word alternative is not the adopted choice.

8. **Direct full seed on the original model**: ff928ef0ecce adopts KSeedDirect222, used by KEndpoint.lean:40. KSeedModel222 and KIndisc222 are absent at the pin, with stable interface definitions moved to KSeedInterface222. This is not a remaining semantic-quotient removal opportunity.

9. **Further source golf and dead-layer deletion**: subsequent commits shorten many Lean proof scripts, combine two paired Rocq dispatch scripts and remove Rocq's unused s0-based enumerator lemmas. These changes are included in the current census. They do not change the literal machine or final statement.

## Verification boundary and documentary mismatch

The verification/simplification README and proposals catalogue contain historical status statements. In particular, their descriptions of direct seed, normalized Rocq certificates, computed trees and quotient unification as pending must not overrule the current source and later integration commits.

The integration commits report selective serial Lean builds. Their descriptions explicitly leave KEndpoint21x, the remaining source-certificate chunks or the site batches to a full rebuild as applicable. Phase-15 receipts bind their historical bytes, not every later source edit. This review found no new all-current Lean endpoint evidence among those integration commits.

The normalized Rocq adoption reports the full 215 compile order through CorrectDense215 under Rocq 9.1, with closed endpoint assumptions; it explicitly says recursive coqchk was not rerun. Later commits report narrower current slices and endpoint rechecks against an already compiled reference. These are repository-reported checks, not checks independently performed here. A matching current recursive kernel audit remains the acceptance gate, not an automatically inherited consequence of old coqchk logs.

No claim is made here about an internal PA/ZFC derivation, a new smaller machine, unconditional Con(ZFC), new compiler speed or proof-object-size reduction.

## Remaining opportunities and duplication filter

- The previous report's guarded left-frame contract, 35 runtime templates and prospective 4,789 expensive obligations are already an archived proposal. They are not newly integrated, and must not be rediscovered as a new contribution.
- Shared EnumStack proofs and a generic/cofinal scheduler were already proposed. The present enumerators still duplicate drain/reach arguments, but reuse alone is not a new mathematical proposal.
- The canonical 89-cell Rocq common-macro graph, closed-support transport, AX-word sharing and direct-Infinity route are already existing component proposals. Production adoption may be useful, but should be described as integration rather than new research.
- The newer **generic-spine import cut** is distinct from quotient unification: after the quotient itself has been unified, four mixed generic/CP-specific modules still keep six CP facades in the K215 closure. An independent overlay import census confirms 174 to 168 modules, 1,752,650 to 1,725,295 bytes and 37,648 to 37,117 lines, with no unresolved project imports. Current QuotientModel.memberForm is exactly an abbreviation of KQ1Model.memberForm, and its satisfaction theorem simply forwards to KQ1Model, so that particular facade bypass is justified by direct source inspection. This remains an **uncompiled candidate**, and retained compatibility adapters increase aggregate maintained source rather than reducing it.
- A generic compiler algebra for EnumPerm/EnumDom was considered but is not recommended as a headline result. Their direct compile proofs are only approximately 30 and 37 lines. A new 12-field interface plus both adapters can consume the apparent duplication saving. Count shared helper and wrapper costs and do not pull EnumDom into K215 merely to alias code.

## Replay and package scope

Run:

    python -I -B verify_sources.py

The script reads only the immutable snapshots and manifest, prints the measured result and modifies no files. It runs neither Lean nor Rocq and executes no repository generator, receipt reader or supplied script. The commit messages in relevant_commit_claims.json are inert provenance for the reported historical check scope.

Files:
- source_manifest.json: pinned URLs, SHA-256, Git blobs for current sources, imports and metrics.
- snapshots/current/: exact 174-module current endpoint closure.
- The 178-module baseline is a compact source/import/hash ledger in source_manifest.json, not a bundled second source tree.
- endpoint_delta.json: removed/added modules and exact metrics.
- generic_spine_independent_review.json: independent static candidate import-census result.
- relevant_commit_claims.json: selected integration messages and verified commit URLs.
- verify_sources.py: owned read-only verifier.

Original source notices are retained in the snapshots; preserve the repository and inherited notices when repackaging.
