# Independent review: finite pointwise conjugacy lift

`DirectBFSConjugacyLift.lean` derives pointwise finite statements from the previously accepted seven aggregate Boolean facts. On natural indices below the appropriate bounds it states:

```text
rename(original.getD i default) = direct.getD (rowMap.getD i 0) default  (i<943)
rowMap.getD (rowInverse.getD i 0) 0 = i                              (i<943)
horizontal.getD (horizontalInverse.getD i 0) 0 = i                   (i<250)
vertical.getD (verticalInverse.getD i 0) 0 = i                       (i<439)
```

It also proves that both forward and backward arrays land in range. It then packages the maps as `Fin 943`, `Fin 250`, and `Fin 439` functions. `rowForward` maps **original row indices to direct row indices**; the horizontal and vertical forward maps rename original colors to direct colors. The explicitly stated inverse equations have the form `forward(backward(i))=i`; the bijectivity proofs infer injectivity from surjectivity on each finite type. The three `Function.Bijective` conclusions are about the **forward** maps. `row_match_fin` applies the pointwise equality to a finite original row index, retaining the `getD` defaults in the exact statement. It is a standard finite Lean result; lifting it to arbitrary model-valued tile indices, obtaining row/edge-word correspondence, and machine semantics are separate.

`check.py` verifies accepted `observations/directbfsconjugacylift-attempt02/terminal.json`, current and copied source, `run-v2.py`, logs and object, pre/post pins, all eleven exact reported axiom lists, both selected direct imports and all 59 recorded stage receipts. It also invokes the independent accepted aggregate **receipt** audit, which checks the successful outer process and 60 providers without replaying Lean. The selected aggregate object is the exact reviewed retry object `/tmp/direct-bfs-aggregate-retry-ej6z9xcm/DirectBFSCoverageAggregate.olean`, SHA `1e8286158838654f19d7de3ba4ca45b99b72eda814546188e0a982b6c84af02b`; the other direct input is `DirectBFSConjugacyShape.olean`. Exact paths and hashes appear in `check-output.txt`. Accepted source SHA `fa709d15826bf52ca2d8da275cedf97912ead112ef2a7afa6643e717028c6761`; object SHA `4ff48994bfef89bf7bce5e1473a261dd7eb19e07fd579cd7658dede08716c39e`.

The three bijectivity reports list `[propext, Classical.choice, Quot.sound]`; the eight remaining reported pointwise statements list `[propext, Quot.sound]`. Accepted source has no `sorry` or `admit`, and its log has no error, warning or `sorryAx`. The failed attempt01 is independently verified to exit Lean 1 and contain recursion-depth errors and `sorryAx`; its archived source differs from accepted source only by the added `set_option maxRecDepth 16384`. The author runner writes the terminal before its final diagnostics/pin checks, so this audit separately examines their recorded evidence; it does not reconstruct an unrecorded outer runner exit.

No Lean replay was performed. The result does not establish full transitive provider selection, source-object/package/dynamic-library ancestry, external JSON/PDF byte binding, a model-level word transfer, a halt equivalence, or a syntactic iPRA proof.
