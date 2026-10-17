# Register-role coalescing: a concrete, unsuccessful state-reduction experiment

**Result:** this experiment does not improve the 252-state machine. It removes 598 transfer-loop occurrences at the register-program level, but its frozen implementation loses too much shared decoder structure. The same complete compiler emits 314 states for the original control and 888 states for the transformed control. Both complete binary tables are included as measured controls; neither is a new consistency-calibrated candidate.

All source inputs are pinned to `VladimirReshetnikov/ProveIt` revision `beb2c633ae57a0883d28fb6d0c75342d08cfdeda`. `input-provenance.json` gives exact input hashes, including Git blob identifiers. The source files retain their upstream attribution. This research started from Mira-Cult's register program, Jeff's verification, Wade's compiler framework, and the repository's later register-permutation/phase-analysis work.

## Idea and invariant

A transfer loop with distinct source and destination registers implements

\[
(R_s,R_t)=(a,0)\longmapsto(0,a).
\]

If a physical slot already holding `a` can be assigned to the destination role after the loop, that transfer can become a change of interpretation with no tape updates. Register roles may receive different physical slots at different source-control sites. This is stronger than choosing one fixed permutation for the whole program.

The essential storage invariant is explicit: every live logical role occupies its assigned physical slot, every omitted logical role is zero, and every unused physical slot is zero. Ordinary interference coloring by itself would be insufficient. In particular, an increment of a previously zero role must use an actually zero slot; a retained transfer must have distinct physical operands and a zero physical destination; and every cross-edge change of assignment must preserve all nine physical values.

`allocation_certificate.py` checks each coarse-graph edge as an exact affine equation on all nine physical slots, under the source mask and decrement guard. It checks both directions' physical decrement operand agree, that initial all-zero storage satisfies the encoding, that every color is in `0..8`, that live colors are distinct, and that the unique terminal control site is the original halt. It uses no numerical samples. The independently checked source masks and transfer-entry shapes supply the assumptions; those audits are in the accompanying `proof_audit` artifacts.

Silent transitions also require a progress condition. The independent epsilon audit finds 1,555 erased/control edges, no directed epsilon cycle, and a longest consecutive epsilon chain of four. Consequently copy erasure cannot introduce an infinite run consisting only of erased transitions. This is an ordinary finite-certificate argument, not a new Lean kernel theorem or a newly formalized binary-machine calibration theorem.

## Frozen counts

| Stage | Measured result |
|---|---:|
| Literal source instruction sites / guarded cases | 6,460 / 8,391 |
| Simple transfer-loop occurrences | 972 |
| Occurrences with a certified zero destination at external entry | 970 |
| Coarse graph sites / edges | 4,520 / 5,480 |
| Potentially nonzero role instances | 35,719 |
| Initial storage live ranges / interference edges | 1,385 / 9,157 |
| Nontrivial eligible value-transfer edges | 968 |
| Greedy nontrivial coalescences | 596 |
| Erased transfer occurrences, including two with a zero source | 598 |
| Retained transfer occurrences | 372 |
| Coalesced storage live ranges / physical colors | 789 / 9 |
| Original shared decoder nodes | 203 |
| Frozen allocated decoder nodes | 917 |
| Nodes after removing all 598 generated no-ops | 778 |
| Exact guarded control cases checked after compaction | 5,999 |

The frozen allocation is **unweighted optimistic greedy coalescing with seed zero**, followed by a verified nine-color DSATUR coloring. `freeze_allocation.py` reconstructs this specific result directly. The broad experimental `static_coalescing.py` entry point searches additional seeds and must not be confused with the frozen replay.

`allocated_dag.py` reconstructs shared binary control from the site allocation and exact primitive recipes. `compact_allocated_dag.py` removes generated `B0` leaves only after checking the successors of all remaining guarded cases. All 598 no-ops can be removed in this variant, and no existing break/continue operand requires rebasing. A separate decoder/path-arithmetic audit independently checks the result, including unconsumed zero PC suffixes and the unique halt.

## Complete compiled controls

| Component | Original control | Coalesced control |
|---|---:|---:|
| Decoder | 203 | 778 |
| Fresh compact initializer | 44 | 43 |
| Shared literal engine | 44 | 44 |
| Arithmetic/control leaves | 19 | 19 |
| Break scans | 1 | 1 |
| Continue scans | 3 | 3 |
| **Total working states** | **314** | **888** |
| Binary transition rows | 628 | 1,776 |
| Symbolic guarded site cases checked | 8,391 | 5,999 |
| Concrete all-zero-tape boot steps | 292 | 268 |

The assembler checks arbitrary register boxes and its affine gap parameter at each site. The fresh boot reaches nine zero register blocks with eleven marked cells and no spare blocks. These are complete charged tables, not estimates obtained by subtracting source-level instruction counts. The increase is 574 states under the same assembler. The optimized upstream 252-state construction is a separate compilation/bootstrap result, so 314 and 888 should not be mistaken for direct competitors with the same optimizations.

Exact table hashes:

- `frozen/original_control.tm`: `242c7278c1f78bd510c8bcec5704e26844dc7f1b99df6185bee2ff33569e9984`
- `frozen/coalesced_control.tm`: `57c87c4f5a87338bd8dd1750972ccf4141d905bd2f430b43a43d452b390ce955`

`frozen/complete-table-controls.json` records counts, per-site checks, bootstrap evidence, compiler hash, source hashes, and explicit proof limitations. Its historical `upstream_commit` field names the older Jeff literal-machine snapshot, not the ProveIt revision used for this experiment; the outer provenance is the pin stated above.

## Bounded diagnostics and implications

Full propagation of dynamic slot permutations, canonicalized among registers with equal certified singleton values, reached the imposed 1,500,000-node limit with 47,626 frontier nodes after visiting only 449 source sites. This is a partial exploration, not evidence that every dynamic-renaming scheme is large. `dynamic-renaming-summary.json` retains the summary and all transfer-entry records; the 54 MB full state list is deliberately omitted.

A bounded search over 232 distinct subsets of the eleven transfer families, with a logical-slot color preference, found a best decoder of 209 nodes. That result selects no nontrivial transfer family and erases only the two source-zero transfers. It does not prove optimality over allocations, family sets, register encodings, or compiler architectures. The complete records are in `coalescing-family-search.json`.

Independent stronger analyses were also tried: exact values below thresholds 3, 4, 8, 16, and 32 with a high-value bucket; and rational affine-hull analysis, both alone and reduced with the singleton masks. The reduced analysis still excludes exactly the six already known guarded source cases, numbered 8202, 8203, 8204, 8358, 8359, and 8360. It automatically discovers the relation `TW = p1 + s1` at case 8390 but yields no extra guard removal.

The useful research conclusion is that maximizing eliminated transfer occurrences is a poor objective for this decoder. A future search should charge shared decoder nodes directly and constrain register assignments at shared subgraphs. That is a concrete direction suggested by the measured failure, not a claimed sub-252 construction. The ordinary copy-erasure invariant and finite certificates can be reused in such a search.

## Reproduction

Tested with Python 3.12. Only the Python standard library is needed; no network calls, solver, Lean, Coq, or external packages are used by this experiment's replay. The table compiler additionally needs these files in a checkout or materialization of the pinned ProveIt revision:

- `Computability/BusyBeaver/Research/ZFC/mira_backend.py`
- `Computability/BusyBeaver/Research/ZFC/recover_wade_dag.py`
- `lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm`

Run from any directory, substituting actual absolute paths:

```sh
python3 /path/to/machine_reduction/replay.py /path/to/ProveIt
```

This sequentially runs `freeze_allocation.py`, `allocation_certificate.py`, `allocated_dag.py`, `compact_allocated_dag.py`, and `compile_controls.py`, then compares all seven main output hashes with the frozen values. The included `value-analysis-32.json` supplies the finite mask certificate. To recompute that invariant first, add `--recompute-masks`; the elapsed-time metadata in its JSON will change, while the frozen core outputs remain identical.

Optional diagnostic reruns:

```sh
python3 /path/to/machine_reduction/value_analysis.py 3 4 8 16 32
python3 /path/to/machine_reduction/affine_analysis.py
python3 /path/to/machine_reduction/affine_analysis.py --reduced
python3 /path/to/machine_reduction/coalescing_family_search.py
python3 /path/to/machine_reduction/dynamic_renaming.py 1500000
```

The final command recreates the large full-state JSON and is unnecessary for the core replay. Optional diagnostic timings are descriptive rather than deterministic. `artifact_inventory.json` separates minimal dependencies, frozen outputs, optional diagnostics, and intentionally omitted files. `frozen/SHA256SUMS.json` pins the exact delivered core variant.
