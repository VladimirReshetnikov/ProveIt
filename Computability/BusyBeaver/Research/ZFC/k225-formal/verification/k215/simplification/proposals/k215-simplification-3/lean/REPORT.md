# Lean K215 proof simplification: source-grounded assessment

## Executive result (updated after the latest-main recheck)

**Latest targeted source check: `e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`, fetched at 18:22–18:24 UTC on 2026-10-21. The major reverse-certificate improvement identified below has now landed upstream. It must not be presented as a new proposal.** See `LATEST_ADDENDUM.md` and `latest_status.json`.

The new upstream implementation adds general signed `OBisim.symm` and `ocheck_halts_iff`, removes the 16 backward-check imports, and reduces `KSource215Data` from 653,569 to 456,548 UTF-8 bytes. The 2,240-entry forward certificate is unchanged and still has only zero offsets. The included zero-offset projection is now a **superseded, uncompiled alternative**, not a recommended additional patch.

The 16 removed checks cost **1,118.739 seconds (18.65 minutes)** in the published original full build, **24.94%** of its successful compilation time. This is measured historical work eliminated by the source change, **not a measured new build speedup**. No new build was established by this targeted recheck.

The best remaining small improvement is import hygiene: all nine site-check batch headers still import the whole source-equivalence proof when they only need its data. Narrow those imports and preserve the old import at the facade. This avoids rechecking approximately **28.2 minutes** of historical site computations after a source-proof-only change. The compact coverage assembly is now also implemented upstream. The strongest further source-check proposal is a canonical-site relation, followed by measured checked sharing; balanced site-table reuse is a separate low-risk runtime lead.

For a new 215-state variant differing by a few local transitions, transport the already proved literal-machine endpoint through a small, invariant-restricted, positive-stuttering simulation. This is cheaper in *new proof obligations* than generating a second bootstrap/source/sites/calculus tower. It does not remove the original proof from the trusted import closure or erase its clean-build cost.

## Latest phase-four baseline (not a new proposal)

A further targeted read at the same e0b8 pin confirms the published phase-four receipt: **185 primary modules, 10 freshly compiled and 175 reused with source/dependency/object/log hash bindings**, both typed clients passing, ten standard-axiom reports and zero audit warnings. This is published **incremental** validation, not a fresh full replay performed here. The receipt also notes 31 selected source-module linter warnings. The original 204-module timings below remain historical.

Current exact UTF-8 sizes are `DomRho8` **30,114 bytes / 517 lines**, `L2AxiomsPerm` **7,563 / 161**, `KSites215` **14,916 / 235**, and `EnumPerm` **22,788 / 545**. In particular, the old 107,243-byte / 754-line site facade has **already been replaced** by direct composition of the same 105 checked blocks. The nine batches and all 4,751 leaf checks are unchanged. General halting-prefix cancellation (`hn_after`, reused by `seg_hn`) and the enumerator shared-command symbolic executor are also already implemented. Do not propose these again. Exact fetched source hashes and receipt snapshots are in `latest_phase4_status.json` and `latest/phase{3,4}_*.md`.

Sources: [phase-four complete-closure incremental receipt](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase4/lean/README.md), [phase-four simplifications](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase4/README.md), [phase-three facade compression](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase3/README.md).

## Further data-tested simplification

The follow-on audit in [`profiling/README.md`](profiling/README.md) independently reconstructs the latest literal Lean trees. The 2,240 source-certificate entries contain 814 aliases of just 1,426 canonical paired test/halt sites. Their entire register-count block CFG is identical, so a new canonical-row checker can reuse `RMBisim.Bisim.halts_iff` rather than introducing a new semantics proof. Existing structured run/transfer lemmas also suffice to commute the two shared increment-pair templates. Four portable Python scripts passed, with explicit optimized-mode rejection; neither proposed Lean adapter is compiled. The same audit measures repeated decoder/site/segment queries and shows why site coverage cannot simply forget continuation prefixes.

## Scope and verification status

- Historical checkout `/research_sub246/source` was not edited. Its working-tree HEAD remains `7ba1598461c6e485c5aeb8f673c0b1d571f8012b`.
- Main source and recorded build evidence were inspected at pinned commit `b6fb232916d008383e7cf2990d68ddb30fded7db`, using cached Git objects and the connected GitHub file reader. A separate snapshot is included under `snapshot/`.
- Later source changes were inspected at `021d848979b670f702cd92ae7bb85ea888847742`, `e29d22cf`, and `c9dc7932`. Their source changes are classified below as **already implemented**, not new proposals. I did not run or independently establish a fresh full build for those later revisions.
- No Lean or Lake executable was found on PATH or in the inspected usual installation locations. **No Lean compilation was performed during this investigation.** The included projection draft and import patch are explicitly uncompiled.
- The local completed tests are source/certificate parsing, exact mirror comparison, published-log aggregation, import/reference inspection, and static diff checks. They are not kernel proofs.

The original [full-build record](https://github.com/VladimirReshetnikov/ProveIt/blob/613f9cf28ac36eaa929f7ef909b0eb7905facc5d/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/README.md) reports 204 project modules and two endpoint clients, with only `propext`, `Classical.choice`, and `Quot.sound`. The later [simplification record](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/lean/README.md) reports hash-bound incremental validation of 201 primary modules plus 14 legacy modules and the two clients. It explicitly does not claim a new full replay.

## What is already done

Do not propose the following as though they were new. Items 1–4 record the earlier b6fb232 milestone; the smaller current phase-four values above supersede their source sizes:

1. **Dominated-rho8 proof pruning and substitution sharing.** `DomRho8.lean` has already fallen from 689,857 to 135,417 bytes, retaining 674 of 3,728 proof nodes and 994 of 5,160 input terms. Each retained theorem is checked directly. The published local API/source check took 8.681 seconds. Public `DomImp`, `le_l`, `le_r`, `sub`, `rho8_all` interfaces are preserved.
2. **AX word reflection at the macro level.** `L2AxiomsPerm.lean` already replaces 1,196 lines / 202,222 bytes with 223 lines / 10,091 bytes. `AXAtom`, `axWordCheck`, `axWordEval`, `axWordRun` compose 156 macro links and retain `l236`, `c236`, `ax_eval` contracts. This is exactly the right abstraction level for shortening this routine.
3. **Generic root iteration and run transfer.** `RMDagIteration.iter_halts_iff` replaces copied iteration inductions; `RMTransfer` and `Dag219Bisim` share program transfer and isolate the legacy seed facade. At b6fb232, K215 imported 201 rather than 204 project modules.
4. **Partitioned source checking.** `KSource215Data` plus 16 forward and 16 backward check modules already fix the old monolithic 900-second timeout. Smaller independent files are a resource/recovery improvement, not proof compression by themselves.
5. **General seed theorem, later than b6fb232.** At [021d848](https://github.com/VladimirReshetnikov/ProveIt/blob/021d848979b670f702cd92ae7bb85ea888847742/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumPerm.lean), `EnumPerm.halts_iff` handles any state between candidates with derivable working registers. `SeedPerm.seed_iff` is reduced to an application rather than duplicating the cofinal enumeration argument.
6. **Factored dispatch, later than b6fb232.** At [c9dc7932](https://github.com/VladimirReshetnikov/ProveIt/blob/c9dc7932/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2RootPerm.lean), `dec_brk`, `pass`, and `fall` compress DROP/MP/AX dispatch proofs. The intervening e29d22cf change adjusts the root proof to use the command decoder/cstep interface.

Sources: [overall simplification record](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/README.md), [direct rho8 proof](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean), [AX word](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2AxiomsPerm.lean).

## Where the real costs are

The published successful original build attempts sum to **4,485.409 seconds = 74.76 minutes**. Failed attempts total an additional 974.845 seconds and must not be counted as successful proof checking. The largest failure was the old monolithic source module at 900.17 seconds.

| Component | Successful original build seconds | Notes |
|---|---:|---|
| Source equivalence, all 34 modules | 2,291.521 | 51.1% of total |
| Forward source checks alone | 1,087.662 | 16 modules |
| Backward source checks alone | 1,118.739 | 16 modules; duplication target |
| Source data | 84.052 | Literal trees, DAG well-formedness and both certificates |
| Sites, all 10 modules | 1,701.227 | 37.9% of total |
| Site-check batches alone | 1,692.447 | 4,751 leaves, 105 blocks in nine modules |
| Bootstrap, 14 modules | 111.374 | 95,714 TM steps, 13 chunks |
| Original pre-compression rho8 | 32.731 | Much smaller runtime cost than certificates |
| Original pre-compression AX | 17.509 | Source size was large, time was not dominant |
| All other successful modules | 331.047 | Includes generic logic and semantic endpoints |

Source equivalence plus sites account for **89.02%** of successful baseline compiler time. A visually dramatic reduction in generated proof lines is not necessarily a runtime improvement. In particular, the compact AX source's separately recorded local check is 38.660 seconds; it should not be advertised as faster than the original 17.509-second module without a controlled comparison.

Measured selected-source sizes at b6fb232:

- `KSource215Data.lean`: 653,569 bytes, 4,854 lines.
- Complete KSource215 group: 665,978 bytes.
- Complete KSites215 group: 158,771 bytes; its facade alone is 107,243 bytes / 754 lines, largely repeated path literals and joins.
- Complete KBoot215 group: 23,502 bytes.
- `DomRho8.lean`: 135,417 bytes, 1,970 lines.

The b6fb232 primary closure had 201 modules, of which 117 lay under generic `KEndpoint`; 84 were additional to that generic closure. These counts predate the latest forward-only source change. These are dependency counts, not disjoint semantic categories and not an estimate of reducible foundational work.

Evidence: [published attempts ledger](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/actual/attempts.json), [final original review](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/actual/final-review.json), local `baseline_timing_summary.json` and `selected_module_sizes.json`.

## Now implemented upstream: eliminate reverse source certificates

The analysis below records the diagnosis against b6fb232 and the initially proposed minimal zero-offset route. Latest main instead implements the general signed-symmetry alternative described at the end of this section. Do not implement the included zero-offset draft on top merely to duplicate that result.

### The exact duplication

[`KSource215Data`](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean#L299) contains 16 `fwd` and 16 `bwd` certificate chunks. Independent literal parsing establishes:

- 2,240 entries in each direction;
- every forward offset is 0;
- the backward list is exactly `(b,a,-z,positiveSuccessor,zeroSuccessor)` applied to each forward entry;
- maximum forward test-site path length 45 bits and maximum structured-target test-site path length **176 bits**;
- the backward section is 197,043 bytes / 2,278 lines, about 30.15% of the entire data module.

At the historical b6fb232 pin, `KSource215.p215_halts_iff` called `ocheck_halts` once for each direction. Meanwhile [`RMBisim`](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMBisim.lean#L339) already supplies `BranchGood.symm`, `Bisim.symm`, and `Bisim.halts_iff`.

### Minimal implementation

Keep `RMOffsetBisim`'s existing forward checker unchanged:

1. Prove `OBranchGood ... A B 0 → BranchGood ... A B` whenever the relation's offsets are all zero. A branch's next offset is zero by the relation assumption; its integer count equation therefore gives equality of natural increment counts.
2. Lift that lemma to `OBisim.toBisim`, using `S0 A B := S A B 0`.
3. Prove a tiny certificate lemma: `allO (fun x => decide (x.offset = 0)) T = true` implies every `ORel T` witness has zero offset, via existing `lookupO_all`.
4. Instantiate with the already checked forward certificate and use existing `Bisim.halts_iff`.
5. Remove `bwd*` data and imports from the primary endpoint closure; keep legacy wrappers if API compatibility is required elsewhere.

`ZeroOffsetProjection.uncompiled.lean` is a proposed source draft, **not compiler-validated**. Its mathematical obligation is a local projection of already proved semantic predicates, not an additional machine-specific induction.

Do **not** blindly switch this certificate to the old ordinary `RMBisim` checker: that checker's `decode` uses 128 iterations, whereas this target has 176-bit pointers. The projection preserves `RMOffsetBisim.odecode`'s 512-iteration support and avoids changing existing decoder behavior.

An alternative, useful for other K-family machines with genuine offsets, is a general `OBisim.symm` under `Srev A B z := S B A (-z)`, using `delta (-z) i = -delta z i`, followed by `OBisim.halts_iff`. This avoids the zero test and generalizes to K221, whose source uses nonzero offsets. The zero projection is the smaller candidate-specific risk; signed symmetry is the better reusable library endpoint. Neither has been compiled here.

## Proposal 2: separate stable program data from expensive proof dependencies

Every `KSites215Batch000` through `008` starts with `import BusyBeaver.ZFC.KSource215`. The batches reference only `KSource215.t215`; the final coverage facade additionally uses `p215` and `t215_eq`. All three declarations already live in `KSource215Data`.

Immediate minimal patch:

- change nine batch imports to `KSource215Data`;
- explicitly retain `KSource215` at the `KSites215` facade to preserve its former transitive interface;
- leave every theorem body, statement and check exactly unchanged.

The included `site_import_split.uncompiled.patch` implements only these import changes. `site_import_static_audit.json` records the source-only checks; this is not a compiled patch.

Follow-up split: extract `p215Nodes`, `p215`, `t215`, `t215_eq` into a stable program-data module; keep `tD`, the DAG well-formedness proof, and source-equivalence certificates in separate modules. This prevents certificate optimization from invalidating site checks merely because the mixed data file changed. More modules can mean a cleaner, cheaper build than fewer modules.

Source: [one representative site batch](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch000.lean#L1).

## Further proposals: canonical source rows and checked sharing

The next worthwhile research target is checker work, not another large tactic script:

- **Already implemented, not new:** direct composition of the 105 checked blocks has reduced `KSites215` to 235 lines. Preserve these existing opaque premises rather than redoing the facade compression.
- **New preferred route:** use the 1,426 canonical-site rows demonstrated in `profiling/`, replacing the raw-path relation but reusing the existing segment-bisimulation soundness proof. The data-only prototype generates and validates a 161,429-byte JSON certificate and rejects four targeted corruptions. A Lean Boolean checker and its soundness proof are sketched, not compiled.
- In source certificates, `oentryOk` decodes two site paths, finds sites by tree traversal, then `obranchOk` recomputes segments. `RMBisim.seg` walks through increment/break/continue leaves until the next test using fuel 1,000. Precompute unique segment summaries, check each once, and have the bisimulation certificate refer to their IDs. Prove summary composition once and retain segment proofs as opaque theorems. This is memoization with soundness evidence, not trust in a Python cache.
- For sites, investigate hash-consing symbolic execution states and common prefixes/suffixes across the 4,751 leaves. Each reused subtrace must carry its branch hypothesis and symbolic tape/box context. Path-dependent operations cannot be merged merely because the decoder DAG node matches.
- Keep finite checks chunked. Tune chunk sizes using actual worst-case kernel time, not number of lines or equal leaf counts: historical successful site batches ranged from roughly 80 to 264 seconds.

These are larger engineering proposals, not measured speedups. A compact certificate still has to check enough information to bind its result to the **literal** machine and source tree.

## Reflection versus direct proof: what not to do

The rho8 history already tested generic interpreter, array, and Boolean-reflection versions. Several full checks timed out at 120–190 seconds or were killed; the accepted reduced direct proof finished in 8.681 seconds. Lean's kernel does not automatically share all evaluator subcomputations as an optimized native interpreter would.

Therefore:

- prefer a small generic soundness theorem plus *chunked* checked data where the repeated computation is genuinely reduced;
- use named opaque theorem boundaries for reuse;
- preserve direct compact proof DAGs when they outperform a monolithic reflected evaluator;
- do not replace `decide +kernel` by `native_decide` and claim the same trust boundary without explicitly analyzing the new trusted computation assumptions;
- do not infer machine correctness from Python acceptance or a long successful execution trace.

Evidence: [rho8 experiment record](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/lean-rho8/history/experiments.json).

## Stable theorem interfaces to preserve

The existing architecture is already good at separating semantics from machine data. Preserve these interfaces while refactoring internals:

- `KEndpoint215.blank_halts_iff_zfc_refutation : BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot` and its nonhalting companion.
- Generic `KEndpoint.blank_halts_iff_zfc_refutation`, with literal-table commuting, terminal-row behavior, `BoxLemmas`, `Covered`, bootstrap reachability/relation, and source-to-calculus equivalence premises.
- `KSource215.p215_halts_iff (R : Registers)` for **every** register file, plus `path_iff_iter`.
- `KSites215.covered`, `KBoot215.boot`, `KDense215.commutes`.
- `L2Perm.l236`, `c236`, `ax_eval`, `root_step`, `iter_iff`, `dagPerm_seed_iff`.
- New general `EnumPerm.halts_iff`, rather than reverting to a seed-specific completeness proof.
- `DomRho8.rho8_all`, not any particular certificate numbering.

`RMTransfer.Closed` permits changed nodes through local contracts and transfers all untouched-node runs by one induction. Use it for changes in the structured register program. Use a TM-level relation for changes in actual machine rows; a register-level rewrite theorem is not by itself a theorem about an altered TM table.

Sources: [generic endpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean), [literal K215 endpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean), [RMTransfer](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMTransfer.lean).

## Transport to CM215 or another locally equivalent candidate

The parent investigation proposes CM215 with state map `phi(176)=52`, identity otherwise, a state-local invariant, and 1-or-3-step simulation. I have assessed the actual Lean interfaces; I have not independently rechecked the CM table or certificate here.

### Use the right notion of tape equality

`Core.Config n` stores:

- `state : Option (Fin n)`;
- `head : Int`;
- `tape : List Int`, the positions containing 1.

A write/restore excursion may reorder the list while preserving all cell values. Thus use extensional tape equality `∀ z, Tape.read b.tape z = Tape.read a.tape z`, not list equality. A relation can conjoin this with equal heads, `b.state = a.state.map phi`, and the relevant invariant on the simulated source configuration.

Existing useful primitives are `Tape.read_write_same`, `Tape.read_write_of_ne`, `Machine.runFrom_add`, `Machine.run_add_eq_runFrom`, and `Machine.runFrom_of_halted`. `Machine.step` is total: a halted configuration remains fixed.

### Generic positive-stuttering theorem

For machines A and B, related initial configurations, and a relation R, require:

1. Related configurations agree on halted versus live status.
2. Every live related A configuration makes one A step that is related to B after **k > 0** B steps (here k is 1 or 3).
3. The source invariant is preserved, so the step premise remains available.

Induction composes finite source runs and target clocks using `runFrom_add`. Forward halting follows from halt agreement. For the converse, if A never halted, the strictly increasing target clock eventually exceeds any proposed B halting time; B's absorbing halt state contradicts relation to a live A state. No fixed global clock bound is needed. Zero-step stuttering would invalidate this argument unless accompanied by an additional well-founded progress measure.

For the finite local checker, explicitly prove a locality/frame theorem: a checked window execution has not read outside its supplied window, its boundary relation holds, and all cells outside its write footprint remain unchanged. Five-cell windows are sufficient only if that footprint/read-bound property is established for the actual 1/3-step templates; finiteness alone does not prove it. Check zero tape, state 0, and exact mapping of halting transitions. A radius-one invariant may be synthesized over 215×8 local triples, with one-step preservation universally quantified over the newly exposed neighboring bit.

`KDenseBridge.Commutes` only transports **one-step** state renaming, so cannot alone justify a three-step rewrite. `KZip` has `Reach1` and reachability composition, but using Core directly avoids introducing another zipper conversion. `ArithmeticPositiveSimulation254` contains the positive-clock argument in an arithmetic-model setting; copying that heavy arithmetic dependency into this endpoint is unnecessary. A small Core-level version is preferable.

Once `BlankHalts new215 ↔ BlankHalts machine215` is proved, the new endpoint is the transitive composition with the established K215 endpoint. This proves a new literal table via a short *relative* certificate, while reusing all the original calculus and bootstrap reasoning.

Source: [Core configuration/run definitions](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/Core.lean#L218), [dense bridge limits](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDenseBridge.lean#L28).

## Recommended implementation order and acceptance gates

1. Verify the now-landed signed OBisim symmetry and forward-only source endpoint with the appropriate compiler/audit evidence. Do not add the superseded zero-offset projection.
2. Keep the forward-only implementation and all public endpoint statements, and narrow the still-unoptimized site imports.
3. Compile every affected dependent and both existing typed endpoint clients. Inspect all axiom reports and exact table/source hashes.
4. Run the repository's serial portable full-closure driver in an initially empty directory using the pinned Lean 4.32.0 toolchain. Honor its machine-wide Lean/Rocq lock and resource limits. Report clean and incremental timings separately.
5. In parallel, prove the Core positive-stuttering/local-window library and attach the finite CM215 certificate. This should not force regeneration of L1/L2/source/bootstrap proofs.
6. Implement the canonical-site relation/checker, preserving `Bisim.halts_iff`, and benchmark checked sharing only where the query profile demonstrates benefit. The facade compression, prefix cancellation and shared enumerator command executor are already in phase four; do not redo them.

Do not present retained baseline objects plus new modules as an independent full closure replay. Do not remove or weaken the typed closed-client audit to make a refactor compile. Keep original logs, failed attempts and machine identities intact.

## Local artifacts

- `source_certificate_audit.json`: exact 2,240/2,240 zero-offset and mirror analysis, with source hash and path bounds.
- `baseline_timing_summary.json`: derived historical module timing summary.
- `selected_module_sizes.json`: sizes for available primary-closure source files, not a claim to cover every repository file.
- `ZeroOffsetProjection.uncompiled.lean`: superseded generic semantic projection alternative; not built or needed after latest upstream signed symmetry.
- `site_import_split.uncompiled.patch`: proposed imports-only change; not built.
- `site_import_static_audit.json`: restricted static patch audit.
- `later/`: selected later seed/dispatch sources, preventing crediting already implemented improvements as new.
- `snapshot/`: pinned source and published validation evidence used for this analysis.
- `latest/`, `latest_status.json`, `latest_headers.json`, `LATEST_ADDENDUM.md`: targeted latest-main recheck.
- `verify_snapshot.py`, `verifier_result.json`, `optimize_rejection.log`: portable source-only audit and its actual run outputs; rejects optimized Python.
