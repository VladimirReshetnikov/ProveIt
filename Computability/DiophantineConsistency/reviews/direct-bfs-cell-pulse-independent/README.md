# Independent review: direct-BFS cell pulse equality

For every `ORingStructure V` model of IΣ₁ and arbitrary `a : V`, the accepted `cell_one` theorem states `packedCell a 1 = packedCell a 0 + Exp.exp (67*1063)`. Its `cell_pulse` corollary takes arbitrary `row,dummy : V → V` and `j : V`, assuming only `dummy j ≤ 1`, and states

```
cellWord row dummy j = cellWord row (fun _ => 0) j
                       + Exp.exp (67*1063) * dummy j.
```

The theorem has no local-word, graph-zero, port, kernel, or Σ₁-definability hypothesis. The bound on `dummy j` is local to the given `j`; lifting this pointwise equality to a definable Boolean perturbation, packing stability or rank calibration is separate work.

`check.py` rehashes source/copies, runner, Lean binary, selected direct providers, object and logs; checks the recorded direct-import snapshots and first resolution; and rehashes 59 chunk receipts. Exact paths are in `check-output.txt`. The accepted object is `d001ed95c02c91dbe3516e2134f3e78b2e55121d644f3e593f96a97601a18ff3`; the two direct imports are `DirectBFSConstructedWord` `383de3016f4801bc91367041049a50b3971c72911542f44e0b7490459675fb88` and `CompactCellPulseEquality` `135ca49eaa24c9959cd0544c30f26c906173e9678bd7845578fc4b84e1dcc358`. Both captured named axiom reports are `[propext, Classical.choice, Quot.sound]` with empty stderr; the runner enforces these reports and rejects coded diagnostics. Its terminal precedes final assertions. The author reports outer exit 0, but no separately retained actual outer-exit receipt was found. No Lean replay or full historical/project/package/dynamic ancestry audit was performed.
