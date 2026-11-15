# Joint forest and ORH local searches

This folder preserves the finite searches that produced the joint-forest
194-state family, together with three unsuccessful reductions of the supplied
PA194ORH machine. It contains portable scripts, frozen inputs, and the completed
search receipts. These are research records; none of the negative searches proves
a global lower bound.

## Results

| Search | Completed scope | Result |
|---|---:|---|
| Joint forest association | 250 operand/MP/loop families | 70 priced at 194, 135 at 195, 45 at 196 |
| Joint forest validation | The 70 families priced at 194 | 63 accepted; seven fail the source-frame checker |
| Novelty of the accepted tables | 63 accepted tables against the pinned corpus | 62 new graph classes; one reproduces PA194ORH |
| ORH inherited-action fusion | 680 candidates | No accepted reduction |
| ORH one-free-action fusion | 143 pair/bit cases; 110,396 candidates | No accepted reduction |
| ORH sole-ingress bypass | 67,164 candidates | No accepted reduction |

The accepted global tables and individual receipts are in
`reference/global_associations/`. The full 250-family record is
`reference/global_associations/summary.json`; `search.log` is the captured log.
The novelty record is `reference/global_associations_novelty.json`. It reports
equality of canonical transition graphs allowing state renaming, a spanning
choice of start, tape reflection, global symbol exchange, and irrelevant actions
on halt edges. Its comparison set has 548 graph classes, with two additional
nonspanning 194-state tables handled separately. Graph novelty does not establish
semantic correctness.

`A0M2L11_194` reproduces the supplied PA194ORH table byte for byte. Its dense table
SHA-256 is
`c16bef7a1587e31adaae747d5bad26721f30bb5c6c33dd4b798be95f5141f1d4`.
All 62 other accepted tables are distinct under the reported graph comparison.
The package's principal construction uses `A0M0L3_194`; its complete construction
and proof material is outside this research folder.

## What the global search varies

`global_associations.py` jointly compiles three binary trees:

1. the four-operand block, with leaves `node32,node53,node55,node65`;
2. the modus-ponens block, with leaves `node75,node37,node6,node54`;
3. the four-increment loop and its return.

There are five binary associations for each four-leaf block and ten retained
associations for the five-leaf loop, giving `5 * 5 * 10 = 250` families. The loop
return is adjusted to its depth, preserving the flattened source instructions.
The compiler shares identical subtrees across these blocks and the axiom reader,
removes structurally unreachable controls, and proposes simultaneous history
folds with the retained matching heuristic.

The price is the raw number of controls minus the proposed number of folds.
It is only a screening score until validation succeeds. For the families priced
at 194, acceptance checks the local folds, equality of the flattened source
instructions, all 4,778 source outcomes, the complete finite-support startup
tape, and dense reachability. Seven families fail source validation at outcome
`[3572,[1,true]]`; they are retained as failures in the summary and have no
accepted machine folder. The 195- and 196-state prices are screening results,
not validated machine claims. This search finds no price below 194.

The source-frame checker uses the retained arithmetic-box contracts. Its results
are executable verification evidence, not an end-to-end Lean proof of the
equivalence with `Con(PA)`. See the package's main proof and verification notes
for the remaining formalization obligations.

## Scope of the unsuccessful ORH searches

`orh_search.py` attempts to fuse ORH control 92 with every non-arithmetic-box
control. Each retained bit action is chosen independently from the two original
controls, giving 680 trials. Every trial is checked against the affected source
outcomes, and a survivor would receive the complete checker. The preserved
record is `reference/orh_merges.json`.

`orh_full/merge_one_free.py` considers pairs outside the arithmetic boxes and
outside controls 74 and 84. If the two controls agree on one bit action, it
identifies the pair, keeps that common action, and tries every write bit,
direction, and remaining-control target for the other action. The 143 pair/bit
cases give `143 * 4 * 193 = 110396` candidates. Halt is not one of the newly
synthesized targets. Its record and captured log are
`reference/orh_full/merge_one_free_results.json` and `merge.log`.

`orh_full/bypass_one.py` deletes an eligible control having exactly one external
incoming transition and replaces that incoming transition by every write,
direction, and remaining-control target. It excludes arithmetic-box controls,
controls 74 and 84, and ingresses whose source lies in an arithmetic box. There
are 89 preliminary candidates and 87 after the last exclusion, giving
`87 * 4 * 193 = 67164` trials. Halt again is not a synthesized target. Its record
and log are `reference/orh_full/bypass_one_results.json` and `bypass.log`.

Both `orh_full` searches use the 4,778 frozen source outcomes, adaptive rejection
ordering, and a symbolic execution fuel limit of 1,500. A rejection therefore
means failure of this specified checker and finite search family. These searches
do not cover arbitrary rewrites, alternate tape representations, or arbitrary
193-state machines.

## Reproduction

Use Python 3.12 (the tested version), with only the standard library. Run from
the package root, or give an absolute script path from any working directory:

```sh
python research/joint_forest/global_associations.py --screen --label screen
python research/joint_forest/global_associations.py --family 0,0,3 --label selected
```

The first command prices all 250 families without validating candidates. The
second reconstructs and validates the selected family. Both write under `runs/`
in this folder, leaving the historical `reference/` results intact. An optional
`--output DIRECTORY` selects a different output directory.

The complete global search and the three ORH searches can be rerun explicitly:

```sh
python research/joint_forest/global_associations.py --label full
python research/joint_forest/orh_search.py
python research/joint_forest/orh_full/merge_one_free.py
python research/joint_forest/orh_full/bypass_one.py
```

The ORH scripts also accept `--output DIRECTORY`. The full searches were not
repeated during packaging; the portable 250-family price screen and the selected
family were replayed. Their compact verification record is
`verification/portability.json`.

## Frozen inputs and dependencies

`inputs/` contains the exact original ORH parent table, ORH table, node map,
grammar, source sites, and source instructions used by these scripts. In
particular, the ORH node map is not silently replaced by the different node map
of the package's principal construction. `PROVENANCE.json` records their hashes.

The scripts use `../../construction/vendor/compiler.py`, `support.py`, and
`symbolic_runtime.py`. These are byte-identical to the corresponding files in
the supplied ORH archive. The compiler's default reference-file loaders are
overridden by the frozen node map and tables before use; no external checkout or
Lean installation is needed. `vendor/engine_foldscreen.py` is copied unchanged
from the same archive. See `NOTICE.md` for attribution.

Only accepted dense tables and receipts are copied for all 63 global families;
large regenerated source JSON and native tables are omitted. A family rerun
regenerates them. `SHA256SUMS` covers this folder's frozen research artifacts.
