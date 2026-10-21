# Source and encoding experiments

This directory preserves exact source transformations and reproducible decoder-prefix allocation prices. It contains **no newly verified consistency-machine table**. The only transition table included here is the inherited K217 input. All changed tables are built in memory solely to measure and verify their prefix allocation.

Run from any directory with Python 3, without `-O`:

```sh
python /path/to/search/source/reproduce.py --output /path/to/output
```

The result is `output/findings.json`. No network, external repository, Python package, or search is required. `SOURCE_PINS.json` pins every included input, source result, and imported upstream module. The exact snapshot is `d3d6b8c14e1ddff37eb1417c5448caa41cfd6da7`. Inherited files and notices retain their original licensing terms; new scripts and prose use the included MIT No Attribution license.

## What is established

| Source | Distinct subtrees | Leaves | Maximum zero run | Prefix-only state count |
|---|---:|---:|---:|---:|
| Inherited K217 | 203 | 4751 | 6 | 217, accepted upstream |
| MP-only transplant | 202 | 4751 | 7 | 220 |
| Retagged K217 | 203 | 4751 | 6 | inherited allocator rejects |
| Residual H or X, consume last U | 210 | 4734 | 7 | 228 |
| Residual H or X, retain dominated A=U+x | 207 | 4738 | 7 | 225 |
| Residual X, reset D in candidate fetch | 209 | 4740 | 7 | 227 |
| Reassociated residual X, consume U | 209 | 4734 | 6 | 227 |
| Reassociated residual X, dominated | 206 | 4738 | 6 | 224 |

The MP-only transplant has exactly the same ordered primitives and complete guarded ordinal control-flow graph as the calibrated MP-only variant reconstructed from K219. Two independent graph algorithms check both successors of every decrement. The input/read schedule is inherited from `source_splice.py`; the improved association is the new result here. Its 202-node source does not imply a 216-state machine: the conservative allocator requires 220 states, and the inherited left scanner does not support its seven-zero addresses.

The retagged layout preserves the entire K217 guarded graph and reduces the number of primitive addresses containing six consecutive zeros from 37 to 27. Break/continue operands may change because they refer to ancestor depth. This remains a source result: the context-sensitive physical allocation rejects the layout. Removing a scanner state is unjustified while any six-zero address remains.

The prefix allocator preserves inherited roles and certifies re-use of retired pure decoder states through their incoming edges. It checks all internal source-prefix decodings. It does **not** establish arithmetic-leaf contracts, blank initialization, preservation of hidden context assumptions, or the complete source-to-binary runtime theorem. The prices are explicitly limited to that scope.

## Residual-counter route

The residual sources explore removing the MP-specific additive field. They modify only the second AX equality gate, and either consume the final U load or retain the dominated relation A=U+x. Logical calibration and a proof compiler are separate obligations, not consequences of the graph checks.

The original second gate, entered with H=A, X=C and D=0, clears the top T exactly when A=C, and clears H and X. Each loop iteration consumes one unit of both H and X. If A>C, the final successful decrement of H leaves A-C-1; if C>A, the final successful decrement of X leaves C-A-1. Equality reaches the clear-T branch directly. Therefore:

* Replacing its unequal H cleanup with `TRANSFER H -> D` returns D=max(A-C-1,0).
* Replacing its unequal X cleanup with `TRANSFER X -> D` returns D=max(C-A-1,0).

Both leave H=X=0 and preserve the old clear-T behavior. Neither returns the absolute difference: the unselected side is cleared. This distinction was caught by direct source execution. The 1,800 probes for A,C<30 included in the reproducer are finite sanity checks; the unbounded equations follow by induction on the paired decrement loop and the three cases above.

The final U load originally copies D into the top and restores D through X. Its consumptive replacement transfers D directly into the top, leaving D=0 before the AX-specific additive read. This allows A to be chosen independently of the old U. It removes four primitive occurrences but creates new distinct subtrees, so the state price increases. The alternative retains A=U+x and resets D in the new-candidate branch; that variant needs its own completeness proof.

The reassociated files preserve the exact primitive word and guarded graph of their corresponding residual variant. They improve the zero run and one prefix state, without approaching 216 states.

## Discovery searches

`searches/` contains the actual search algorithms, with only their input/output paths adapted for portability. They write to `search-output/`, or to the explicit output directory accepted by the residual search. These searches are optional and are not part of the deterministic reproduction command.

```sh
python searches/search_dag_reclaim.py 420
python searches/search_mp.py 420
python searches/search_retag.py 420
python searches/helper_pairs.py
python searches/search_helpers.py
python searches/search_residual.py residual/x-consume.json search-output/residual-consume 240
```

Run these example relative paths from this directory. They remain usable from another directory by supplying full paths. The duration arguments bound exploration by wall time, so the precise visited set can vary with machine speed. The fixed result files are checked without rerunning discovery. The 33-source selector-span family generated no source meeting all of its simultaneous limits; that is a result about the explicitly enumerated family, not a lower bound against other encodings.

The residual searches were stopped after retaining the displayed best sources when two new public 216-state packets arrived. No completed 240-second census is asserted for those interrupted runs. These results precede and do not claim authorship of the later public permuted-command construction, which independently repairs the MP-only read/load association and supplies a full 216-state allocation and runtime proof. See the enclosing report for that development and attribution.
