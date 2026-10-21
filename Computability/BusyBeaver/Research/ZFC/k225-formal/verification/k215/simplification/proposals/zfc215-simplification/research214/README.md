# Reachable-value certificates and bounded 214-state research

This supplement does **not** contain a 214-state candidate. It contributes an independently checked reachable-value invariant for the accepted K215 source, three semantically justified source deletions, and fresh, precisely scoped local searches on twelve final 215-state tables and on M124's new marker selector.

The pinned upstream repository commit is `e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`. The accepted primary source has SHA-256 `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`. Existing numerical-calculus calibration, binary machines, runtime proofs, and earlier search techniques remain inherited work. `provenance.json` and `licenses/` identify that ancestry.

## 1. A finite inductive certificate for reachable source values

The source starts at ordinal 0 with logical registers

    [4, 0, 0, 0, 0, 0, 0, 0, 0].

These are the exact register values reached by the accepted K215 blank bootstrap. For each source ordinal and each of nine registers, the certificate records a subset of the three atoms

    {0}, {1}, {2, 3, 4, ...}.

A bit mask `m` represents the union of the atoms whose bits occur in `m`. `null` marks an unreachable ordinal. At each source ordinal the abstract state is a Cartesian product of the nine recorded sets: no correlation between registers is presumed.

The generator computes the least reachable fixed point in this finite domain, using work-list iteration. The independent checker does **not** repeat that algorithm, and does not import its graph resolver. Instead it:

1. Checks the source hash, full binary source tree, ordinal order, instruction types, and mask domains.
2. Derives control-flow destinations by independently walking ancestor intervals.
3. Checks inclusion of the exact initial registers.
4. Checks that each possible guarded successor is included in the certificate at its target.

For increment and guarded decrement, transfer of an atom is exact. The infinite atom is handled by representatives 2 and 3: their abstract images realize all possible images of any value at least 2 under `+1` and under positive `-1`. No arithmetic operation other than increment, decrement, or identity occurs at this source layer.

### Soundness argument

Let `gamma(I_i)` be the Cartesian-product interpretation at ordinal `i`. The initial configuration belongs to `gamma(I_0)`. Consider a concrete source step from a configuration in `gamma(I_i)`. Its tested register belongs to one of the recorded atoms; the exact abstract transfer includes the concrete output. Every unmodified register stays in its old component. The checked edge inclusion therefore places the successor in `gamma(I_j)`. Induction on the number of source steps proves the certificate for every finite reachable configuration. This is an unbounded invariant argument using a finite check, not a bounded execution experiment. It is an ordinary proof and a Python checker, not a newly compiled Lean or Rocq theorem.

### Exact results

The independent check validates 6,170 abstract edges and 4,194 source/register zero facts. It proves:

| Source ordinal | Instruction | Proved restriction |
|---:|---|---|
| 4671 | `CD 1` | Register 1 equals zero; positive branch is unreachable |
| 4672 | `CI 6` | Entire ordinal unreachable |
| 4673 | `CC 2` | Entire ordinal unreachable |
| 4733 | `CD 6` | Register 6 equals zero; positive branch is unreachable |
| 4734 | `CC 2` | Entire ordinal unreachable |

Thus three whole source ordinals and five guarded cases are unreachable. The invariant applies to the specified calibrated source start. It does not assert these restrictions for arbitrary source frames, all possible initial register tuples, or arbitrary binary tapes.

The union of inherited full-frame runtime row inventories over the remaining source cases, including the four inherited generic block schemas, still contains every one of the 430 physical transition rows. Merely discarding these five guarded cases does not expose an unused physical row. That observation was made against the checked-out saved runtime inventory; the large inventory is not duplicated in this supplement.

### Reproduce

From this directory, with Python 3 and assertions enabled:

```sh
python3 -B code/check_invariant.py inputs/sites215.json results/abstract_source_k2.json
python3 -B code/generate_invariant.py inputs/sites215.json --output /tmp/k215-invariant-new.json
python3 -B code/check_invariant.py inputs/sites215.json /tmp/k215-invariant-new.json
```

## 2. Semantically justified source pruning does not yet save a physical state

Delete the no-op clear-top loop at ordinals `[4671,4674)`, the always-zero decrement and unreachable back edge at `[4733,4735)`, or both. The checked invariant establishes that execution of each removed interval takes one identity step to its exit; the other deleted instructions are never reached. The pruning generator checks the complete old-to-new ordinal map and every reachable guarded edge. All retained opcode operands and control depths stay unchanged in these three constructions.

To prove the pruned source equivalent, relate a retained old ordinal to its new ordinal with identical registers. A retained instruction is simulated by the identical operation and the checked mapped edge, followed, when needed, by the single removed identity step. The invariant excludes entry to a deleted nonzero branch. No infinite execution can consist only of deleted steps, because each removed interval immediately exits. This gives both directions of finite halting equivalence. The conclusion concerns the **source program**, not an allocated binary table.

| Source | Primitive occurrences | Distinct source subtrees |
|---|---:|---:|
| Accepted source | 4,751 | 202 |
| Remove `[4671,4674)` | 4,748 | 203 |
| Remove `[4733,4735)` | 4,749 | 204 |
| Remove both | 4,746 | 205 |

All three retain maximum depth 47 and maximum zero run 6. Removing redundant operations disrupts subtree sharing, which explains why fewer primitive occurrences do not imply a smaller source DAG, much less fewer binary states.

A bounded reassociation beam on the first pruned source visited 13,097 distinct trees and retained minimum DAG count 203. It kept the full inherited partial-selector subtree and checked exact primitive-word and complete guarded-CFG preservation for every saved finalist. This was a time-capped search, not a minimum theorem. Its code, saved finalists, and receipts are retained in `results/pruned3_rotations/`. The receipt stores repeated rotation trees through a lossless shared DAG and records the SHA-256 of the original expanded receipt.

```sh
python3 -B code/prune_source.py --output /tmp/k215-pruned-new
python3 -B code/rotate_pruned.py --source source_variants/pruned3.json \
  --baseline inputs/sites215.json --output /tmp/k215-rotation-new --seconds 75
```

The second output directory must not exist. Because the beam is time-capped, an independent machine can visit a different number of trees. The exact recorded finalists can be inspected without rerunning the search.

## 3. Fresh local searches on final 215-state alternatives

The twelve frozen input tables under `inputs/` comprise commands120, two composed allocations, CM215, ST215, MP-first transfer, rebalanced R41, reencoded K215, two rho6 layouts, zero-spare K215, and zero-spare MP-first. Their exact paths and hashes occur in `results/alternative_folds_summary.json`.

For each table, the search considers pairs of noninitial states for which one read-symbol row is literally shared and the other differs. The changed-read origins must be separated by finite predecessor-derived tape contexts. It then tries both written symbols, both head directions, and all 215 existing target labels for the merged row; references to the removed state are redirected to the retained state. Some specifications have the same effective target after redirection, so counts are of tested specifications, not distinct quotient tables.

The test seeks a positive finite simulation of each old transition, with the exact mapped destination, head displacement, and complete visited tape change. Unknown tape cells branch nondeterministically. A path, node, or context limitation is a failed certificate search, not a semantic counterexample.

The actual initial state is read from each table's header. For both zero-spare tables it is 74; using 0 as an assumed initial state in their predecessor-context computation would not provide the advertised initial-tape coverage.

| Setting | Value |
|---|---:|
| Frozen input tables | 12 |
| Backward context depth | 5 |
| Maximum literal steps per symbolic block | 97 |
| Maximum symbolic nodes per block | 512 |
| Total specifications tested | 947,720 |
| Surviving specifications | 0 |

The earlier single-table probe of final R41 used depth 4, 45 steps, and 200 nodes, tried 71,380 specifications, and also found no survivor. The twelve-table run contains a stronger repeat on that table; it must not be added to the above total as an independent disjoint search.

Example reproduction (substitute each of the twelve input filenames):

```sh
python3 -B code/search_context_merges.py inputs/06_rebalanced.native.tm \
  --output /tmp/k215-r41-folds-new.json --depth 5 --steps 97 --nodes 512
```

Use the filenames actually listed under `inputs/`; the numbered prefix reflects the retained summary order.

## 4. Selective deletion of M124's new helper 127

M124 merges old decoder roles 124 and 127 at 124 and reuses physical label 127 as a predecessor-marker selector. This final search attempts to delete that selector and replace only row `124/0`. There are 214 possible remaining targets, two write symbols, and two directions, giving exactly **856** replacements.

For marker zero, a candidate must reach state 14 at head offset +1. For marker one, it must reach state 62 at offset +1. The current cell is initially zero, the marker is at offset -1, the whole visited tape must be restored, and all outside cells are arbitrary. Recursive visits to `124/0` use the proposed replacement. The existing three-step helper is checked as a positive sanity control before deletion.

No replacement passed both marker cases. The search bounds are 96 transitions after the first row, ten visited cells, and 4,096 symbolic nodes per marker case. Of the 856 first-marker attempts, 851 reached the cell cap, one reached the step cap, three halted or reached the removed/unavailable state, and one passed. That last candidate reached the cell cap on the second marker. These exits do not prove that unrestricted helper reuse is impossible.

```sh
python3 -B code/search_m124_helper_reuse.py --table inputs/m124.native.tm \
  --output /tmp/m124-helper-reuse-new.json
```

## 5. Next constructive target

The evidence favors a joint transformation with two coordinated changes: use source-phase/value invariants to simplify a decoder or arithmetic role, while reallocating the freed row or state to the marker selector. A one-row selector replacement is too restrictive in the finite searches above. A successful 214-state result must include the exact binary table, a proof of the changed source interface or an equivalence to the accepted table, a complete primitive simulation for the new invariant domain, and a matching blank-start argument. None of the failed local searches is a lower bound on state count.
