# Closed-factor pruning audit on the supplied208 source

`python3 -B check_pruning.py` and `python3 -O -B check_pruning.py` replay three exact source-tree edits, independent arithmetic/interval CFG resolution, retained-edge transport, external-entry census and syntactic DAG counts. No208-to207 binary construction is claimed.

The previously checked blank-calibrated source invariant implies R1=0 at ordinal3847 and R6=0 at3891; the branch bodies3848,3849,3892 are unreachable. This packet does not reprove that invariant; its certificate/checker lives in the separate reachable-source bundle. Conditional on those exact source guards:

* Replace subtree001101110 by its right child0011011101, removing the closed transfer loop3847–3849.
* Replace subtree1110011 by its right child11100111, removing the closed clearing loop3891–3892.

There is no external entry into either deleted body. The only external entries into deleted intervals are3841/zero→3847 and3889/zero→3891. Each always-zero CD step leaves every register unchanged and proceeds to the retained successor3850 or3893. Hence delete that stuttering source step, redirect incoming edges, and inductively match all retained source states. The initial ordinal136 is unchanged and belongs to neither interval. A retained halt is preserved. Each deleted segment takes one step under the guards, so there is no infinite hidden internal execution. This is a source-level conditional bisimulation, not a new whole-machine proof.

The exact remaining CFG is checked after deletion using an old-to-new ordinal map: all retained edges equal the original edges followed by the stated bypass. The emitted DAG counts are197 baseline,198 first-only,199 second-only,200 both. Leaf counts are3909,3906,3907,3904. These DAG counts are not Turing-state lower bounds. They demonstrate that fewer executed source primitives do not automatically improve sharing under the existing syntax. In the literal current table the relevant decoder entries19/28 and103/108 are shared by many other source occurrences, so deleting those global states is not justified by these two local source guards.

Inputs are from U208_ConPA_Entry_Context_2026-10-29 at ProveIt commit ef5a23e04b0285e321ceec5f4b329223cee0ab57. Source SHA256 is checked against the receipt. `source_language.py` is the attributed inherited K225/K226/ProveIt syntax utility, not newly authored. This audit is ordinary arithmetic and finite checking, not a proof-assistant certificate.

## Bounded layout discovery

The `search/` scripts explore closed binary reassociations while preserving the entire3908-node internal source-prefix binding. The middle factor of a reassociation must begin with a pure right-reading decoder, so the earlier220 retagging collision is excluded. Guarded lanes edit only high decoder labels (plus89); the wider lane removes that label restriction. A 50-step local prefix-segment cap and fixed beam/layer bounds make these heuristic searches, not lower bounds. Every prospective new fold still needs complete runtime/startup and inherited calibration before use.

The candidate-fold scanner considers opposite predecessor tags, one identical branch, and an existing nonrecursive two-cell helper (40-step cap). The `*_plus.py` and wider versions additionally check exact duplicate rows. The stronger conditional-history208 fold is treated as baseline, not rediscovered or claimed new. No conclusion is drawn about larger windows, additional rewritten helper rows or different source programs.

Optional expensive replays (run from this bundle):

```
python3 search/guarded.py inputs/class_a /tmp/u208-layout-class-a
python3 search/guarded_plus.py inputs/class_b /tmp/u208-layout-class-b
python3 search/wide.py inputs/class_a /tmp/u208-layout-wide
```

These files contain the fixed script version that rejects an internal halt cleanly. Earlier exploratory runs that raised KeyError at halt were restarted; their partial visits are excluded from completed lane counts. Logs are execution receipts, not additional formal certificates. The fast pruning checker does not rerun these searches.

A separate source-only search starts after deleting both loops and applies global closed-factor reassociations, replacing every occurrence of the selected equal subtree. Its8-layer, beam8, seed7 run visits10,218 additional syntax trees. The best DAG count remains200 at every layer; the initial pruned source also has200. This search allows long zero runs and does not emit or validate any binary machine. It is not a lower bound on the source DAG optimum. Optional replay:

```
python3 search/pruned_dag.py inputs/class_a /tmp/pruned-improvement.sites.json
```

The output file is written only if this heuristic finds a DAG below197; none was produced by the supplied run.

Completed literal-table discovery counts (all exit status0):

| Lane | Layers / beam / seed | Additional tables | Additional fold survivors |
|---|---:|---:|---:|
| ClassA guarded |12 /16 /13|1,003|0|
| ClassB guarded + duplicate-row scan |12 /16 /13|1,141|0|
| ClassA wider + duplicate-row scan |8 /16 /13|2,358|0|

The lanes may overlap; their sum is not a count of nonisomorphic machines. `python3 -B check_receipts.py` (also with `-O`) checks log completeness and arithmetic only, explicitly not the search itself. The optional commands above rerun discovery. The sources are the literal208 tables included in Entry_Context, not the underlying209 tables. Prefix admission preserves internal decoding but does not by itself prove engine, history guard, arbitrary-register runtime or blank startup correctness; those would be required for any survivor. There is no survivor to send through those gates.
