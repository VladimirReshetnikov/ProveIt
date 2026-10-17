# Intake review 52 — Searching below 252 states

Reviewed 17 October 2026 by the opening/encoder lane. This is an intake dossier, not a new formal proof or a new machine claim.

## Package, pin, placement and reading scope

- Archive: `docs/incoming/zfc_sub252_research_20261017.zip`.
- Untouched extraction: `/tmp/zfc-intake-158/zfc_sub252_research_20261017/zfc_sub252_research_20261017/`.
- Execution copy: `/tmp/zfc-intake-158/run-52/`.
- Results and full command records: `/tmp/zfc-intake-158/results-52/`.
- Stated ProveIt pin: `beb2c633ae57a0883d28fb6d0c75342d08cfdeda`; upstream literal snapshot `297ab8df7e5de329605c3875b4934643b371a5e3`.
- Current-tree comparison at `80e26b89e905bf3e5dfc322befdc1c6eaf25a109` (maintained Streams files also present in the shared worktree).
- Read the complete 509-line `report.tex`, README, attribution, all three proof-audit notes, semantic-seed notes, machine-reduction notes, and the new scripts. Inspected imported Python code and its I/O/import boundaries before execution. This review did not rebuild or visually inspect the delivered PDF.
- Proposed placement: source 52/addition to the existing `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels` host. It continues the actual 252 candidate, seed and register-allocation questions, and the incoming-action searches. The delivery's suggestion to create a sibling formal-project research directory is document content, not a user instruction, and does not override the incoming procedure.
- Attribution is explicit: new work MIT-0; Mira-Cult's original program/machine, Jeff Ketchersid's verification, Andrew J. Wade's compiler, mira-emmy's public253 reduction, ProveIt contributors and source27's symbolic checker remain credited. No historical priority claim is made for finite-DAG HF realization or compiler coalescing.

## Outcome and proof status

No complete sub-252 machine, no 251 initializer, no new Lean theorem, no internally serialized ZFC derivation and no PA consistency endpoint are delivered. The manuscript says this plainly at `report.tex:54`, `:75`, `:95`, `:383`, and `:484`.

The main mathematical contributions are sound as ordinary arguments with their stated boundaries:

1. **Exact quantifier-free membership criterion** (`report.tex:178–223`). Identify equal variable values, enumerate acyclic membership patterns, and realize every finite DAG as an induced graph of distinct HF sets. For m vertices, use tags t_i={i,m}, then x_i={t_i}∪{x_j:j→i} in topological order. Tags have rank m+1, vertex sets rank at least m+2. This both separates vertices and prevents accidental membership edges. The construction has at most 3m+1 shared set nodes. Foundation gives the converse acyclicity. The three-way set-assignment/HF/pattern equivalence is an ordinary theorem available in ZFC; finite regression is not its proof.
2. **Semantic startup criterion** (`report.tex:249–276`). Use one set-sized ZFC model and truth under every assignment for all initial top/cache/stack formulas. Every original proof-search command preserves that invariant; all-state completeness supplies the reverse implication. Leading universal prefixes may be removed only with all residual free names universally closed. Separate satisfiability of seeds in different models is insufficient. This is a model-relative extension of the soundness argument, conditional on the unchanged full runtime/bootstrap contracts, not an assertion that these seeds have C254 derivations. The combined executable recognizer remains incomplete outside its supported fragment. Its caps return `unsupported` (unknown).
3. **Role-swap and static storage simulation** (`report.tex:281–350`). A complete transfer into a zero destination can become a change of logical-to-physical interpretation. Distinct operands, external macro entry, exact macro exit, no external interior entry, correct halt sites, and zero in unused physical slots are essential. The certificate checks every complete physical vector through each macro edge. Exact singleton masks support canonicalization; the `>=32` bucket does not establish equality of actual values. The transformation's all-zero-root invariant cannot be combined automatically with the broader dirty/semantic starts.
4. **Progress and control compaction** (`report.tex:352–385`). The exact erased/control graph has a rank decreasing on every epsilon edge. This justifies finite epsilon closure for this allocation. The separate compaction audit preserves all guarded successors, data operands, initial control, the unique halt and clean unconsumed PC suffixes. These are finite abstract source certificates; binary simulation remains a separate theorem.
5. **Set-model transfer inside ZFC** (`report.tex:428–470`). The conditional theorem via set-coded soundness/completeness is correct. Constructions must occur inside the given model, even if its membership is externally ill-founded. This is an ordinary ZFC reconstruction route, with the exact model transformations and machine/refutation comparison still to be supplied. It does not automatically turn every Lean metatheorem into a ZFC proof or establish PA-internal proof translation.

The final independence qualification is correct: consistency plus an internal nonhalting↔Con theorem rules out a proof of nonhalting, but consistency alone does not in general rule out proving a false Sigma1 halting assertion.

## Reconciliation with the current tree

The report's principal endpoint claims are appropriately current; it does not resurrect Choice or startup as premises of the existing external 252 theorem.

- `Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md:7–10` states the closed external ZFC equivalence and explicitly leaves PA open. At `:130–156`, it records the completed 3,010-entry program bridge, closed native/ZF/ZFC composition, and the remaining arithmetic proof/trace translations. `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryZFC252.lean:23` and `:28` are the actual halting/refutation and nonhalting/consistency declarations. This agrees with `report.tex:144–150`; the package's baseline audit `remaining_obligations` strings are historical audit scope, not the current theorem status.
- A **stale retained context note** is still visible at `Computability/BusyBeaver/Research/ZFC/safe_initializer_families.md:13–16`: “once its concrete 3,010-entry kernel check completes” and “still pending”. The current candidate README `:132–133` says that exact check has passed. The delivery vendors the former historical note but its report uses the later completed endpoint. Intake should preserve delivered bytes and explain this reconciliation rather than treat the old sentence as a current gap.
- The existing seed certificate is precisely the six constructors at `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SeedInvariant254.lean:18–24`, with C254 soundness at `:40–47`, stack soundness at `:53–56`, and the program theorem at `:67–73`. Its Python recognizer is `Computability/BusyBeaver/Research/ZFC/safe_seed254.py`. The new acyclic-pattern recognizer is a substantive extension of that incomplete recognizer, **not** a proved strict extension of C254 theoremhood. The report correctly avoids that inference.
- Six dirty starts are already checked in `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyReset254.lean:184–194`; `:198–204` proves the candidate3/cache1 immediate halt. The report explicitly treats these as prior work. Its semantic screen may help when those exact numerical conditions fail, but does not replace their continuation proofs.
- The relation `TW=p1+s1` at case8390 is already named in `Computability/BusyBeaver/Research/ZFC/phase-entry/README.md:9–14`. The new affine analysis independently recovers it; it is not a new current-tree relation. The same note `:28–40` already distinguishes completed degree1 action coverage, partial degree2 coverage and the six-guard invariant's unformalized altered-machine scope.
- `Computability/BusyBeaver/Research/ZFC/permutation252_minimization.md:22–27` describes the older separately screened incoming-path family. Its `:71–77` already points to the later compensating **target-only** search. The new write/move/target degree2 family genuinely enlarges that target-only domain by factor16 (1004 versus251 choices per row), but its saved run remains partial. It is not the first repository work permitting compensation or the first full-action degree1 family.
- `Computability/BusyBeaver/Research/ZFC/register_lifetime.md:136–161` already charges complete tables and explicitly leaves new runtime/calibration unverified. The role-allocation report extends those resource-lifetime questions with a different site-dependent allocation and a complete negative compiler measurement; transfer counts cannot be subtracted from the frozen252 table.
- The PA project has advanced beyond a generic “runtime/scheduler only” description: `Logic/Interpretability/ZFCinPA/README.md:314–318` records all-internal accepted-proof transport and the fixed forward consistency implications. `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorConsistencyForward254.lean:65–78` proves the IΣ1/PA forward sentences. Checked configurable encoding, opening, vacuity, alpha and stream composition now supply reverse-compiler infrastructure (`README.md:322–386`; maintained `ValidatorEnvironmentStreams254.lean:114–138`). These do **not** complete the converse or actual binary PA equivalence. The report's unclosed PA endpoint remains accurate. Its easier ZFC model route must not replace the user's original PA target.

## Executed checks

All runs used an independent copy; no delivered file or repository file was edited. No Lean, Coq, proof compiler, version query, dependency build or download was executed. The Python `compile_controls.py` stage is the inspected finite TM-table assembler, not a proof compiler.

The top-level `reproduce.py` and nested `machine_reduction/replay.py` were **not** invoked because they require checksum-manifest verification. Per intake instruction, checksum manifests were ignored completely. Their substantive jobs were run directly. Assertions remained enabled. The driver `/tmp/zfc-intake-158/run52.py` records each exact `uv run --no-project --offline python ...` command, 600-second stage cap, exit code, duration and log in `results-52/commands.json`. The full dynamic exploration additionally had an outer120-second cap and its command is recorded in `dynamic-comparison.json`.

| Run | Result and scope | Seconds |
| --- | --- | ---: |
| baseline | PASS:252 working states/504 rows, all8,391 conditional cases, exact82,552-step blank prefix, all primary zeros, all spares/exterior, first64 register controls |2.669|
| foundation-seeds | PASS:all65,536 round trips;13,962 formulas/4,082 stacks versus13,516/4,051;44 independent probes;23 HF counterassignments;13,966 formula test instances/155,977 V3 valuations; caps and buried falsity controls |3.019|
| hf-embedding | PASS:all4,166 loop-free graphs through4 vertices;573 DAGs realized as distinct induced HF sets |0.164|
| value-masks | PASS:all thresholds3,4,8,16,32; same six excluded guards |2.969|
| frozen-allocation | PASS:seed0 allocation,596 nontrivial coalescences,9 colors |0.966|
| allocation-certificate | PASS:all5,480 edges/4,520 sites;598 erasures,372 transfers;zero-unused slots, initial frame, matching decrement operand and actual halt |0.966|
| allocated-dag | PASS:203→917 shared nodes with exact emitted recipes |0.766|
| compaction | PASS:598 noops removed;917→778 nodes;no control-operand rebasing |0.815|
| machine-controls | PASS:complete original314 and coalesced888 tables;all8,391/5,999 site cases;literal292/268-step clean initializers |4.120|
| role-inputs | PASS:all6,460 leaves match literal source,8,384 feasible transfer inclusions,6 infeasible guards,1 halt;all972 macro boundaries and970 zero-destination entries |0.815|
| epsilon-progress | PASS:1,555 erased/control edges,zero cycles,max chain4;all exact rank decreases |0.114|
| compacted-control | PASS:independent5,999 guarded successor checks,initial entry,unique halt,unchanged data operands,clean suffixes |1.766|
| affine | PASS:exact rational invariant and closure;no extra excluded guard |1.166|
| affine-reduced | PASS:same result with exact singleton-mask reductions |1.266|
| coalescing-families | PASS:all232 declared family choices;best209 nodes with no nontrivial transfer family |52.216|
| joint-actions-bounded | PASS as execution;fresh60-second **partial** run,not the saved historical run |60.125|
| dynamic-renaming1500000 | PASS:full advertised bounded exploration,1,500,000 states,1,452,374 pops,1,817,015 edges,47,626 pending,449 sites;still partial |10.854 inner exploration|

`/tmp/zfc-intake-158/compare52.py` compared substantive regenerated results with the delivery: all seed/witness records, all HF records, all mask values and exclusions, allocation/DAG/compaction records, both affine invariants, all232 family results, all independent audit records, and the two **literal complete table byte strings** agree. Only explicitly variable timing fields and the role audit's source-byte metadata for the recomputed timing-bearing mask file were excluded. Both complete-control evidence records agree. The dynamic replay agrees in all recorded counts, histograms, top sites and all972 occurrence records; its full1.5M list is retained only in the run copy. `comparisons.json` records22 substantive comparisons. No checksum-manifest comparison was done.

The delivered joint record's accounting was separately checked:

- 46×1004²=46,368,736 planned recipes;
- 2,825,507 pruned,43,543,229 remaining,zero survivors;
- all group totals and frontier completion weights agree;
- frontier cylinders are pairwise disjoint within each deletion group.

This is an accounting/algorithm audit, **not** a fresh replay of every saved pruning event. The fresh60-second run used the exact delivered search code, including baseline8,391-case and82,552-step checks, and yielded2,045,111 pruned,44,323,625 remaining,28,107 partial nodes,57,125 checks,zero survivors. It remains `time_bounded_partial`. Unsupported symbolic operations and fuel failures remain diagnostic negatives. The historical243+900-second journal was not rerun to its exact event count. The broad80-seed static-allocation experiment is optional and was not separately rerun; the advertised frozen seed0 and full232-family comparison were.

## Useful ideas for the active task

1. **Broaden original-runtime startup searches with semantic certificates.** This is immediately useful computationally: inspect the exact whole root frame, then accept all top/cache/stack heads certified by the new acyclic-pattern method. Preserve the old syntactic certificate when available. A semantic-only positive still needs a model-relative soundness theorem and a PA-compatible calibration before satisfying the original goal. The report supplies no smaller bootstrap.
2. **Optimize emitted sharing, not the number of transfer occurrences.** The exact314→888 regression is useful evidence against occurrence-local greedy coalescing. Constrain allocations at shared DAG nodes or pay explicitly for every clone and reconciliation. Role changes that cancel within a small region, or maps normalized only by a proved equal-value stabilizer, are focused alternatives. No global lower bound follows from this failure.
3. **Keep zero-unused slots and epsilon rank as reusable certificate interfaces.** Those two invariants close common holes in copy-elimination arguments. The exact rank≤4 is a clean reusable finite progress certificate for this variant, not a license to erase cycles in other variants.
4. **Use current source assumptions when mixing approaches.** Dirty semantic starts and an allocation specialized to the all-zero invariant cannot be united by taking the union of their successful tests. Reestablish the invariant or prove a prefix into it first.

No mathematical blocker was found in the report's scoped ordinary proofs. Its strongest concrete engineering result is a reproducible negative compiler control, while the strongest positive new search aid is the exact semantic seed recognizer. Neither closes the PA endpoint or changes the frozen252-state solution.
