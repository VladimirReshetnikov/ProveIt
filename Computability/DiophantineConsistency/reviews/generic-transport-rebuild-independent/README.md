# Independent review: generic carrier transport rebuild

The retained three-stage run supports the fresh generic helper build under the provider limitations below. `check.py` independently compares historical and new source bytes, rehashes the runner, recorded pins, source snapshots, stage outputs and logs, and checks post-hoc first resolution for every declared direct import. Exact paths and hashes are in `check-output.txt`. No Lean replay or complete serialized transitive-closure audit was performed.

The source changes are exactly:

* `TransportOrder.lean` deletes its first line `import Direct80RankEquality`; its remaining bytes, including `Mathlib.Tactic.Linarith`, are unchanged.
* `CarrierTransport.lean` adds direct imports of `DiophantineConsistency.ArithmeticGcdNormalization` and `DiophantineConsistency.ModelDifferenceRing` after `import TransportOrder`; every remaining byte is unchanged.
* `OffsetBound.lean` is byte-identical to its pinned historical source.

Therefore this chain has no **direct source import** of `Direct80RankEquality`. We did not deserialize or prove the entire transitive closure excludes that module. These are generic conditional arithmetic helpers: for example, `model_nonnegative_of_carrier` concludes `0≤B` only from its explicit sign, size and carrier equations in `DiffRing V`, and `offset_bound` has explicit ordered-ring and discreteness hypotheses. Their compilation alone is not a trace75 transport-sign theorem, machine bridge or iPRA endpoint.

The three recorded stages have inner exit 0 and object hashes `TransportOrder` `6696792c784a1f6dc56e06076350015ca235a8973caf3ecda2a9328128056da2`, `CarrierTransport` `05b15e987fa4eeb289936785ac2aaf7d4d2b0916fe29fd44ad9d52402c9da53d`, and `OffsetBound` `1702af9273f8d0211bc57a013b97fe58c7e58a0791bb4b217f1207c6a27923a4`. External arithmetic/model/tactic objects are pinned, and currently first-resolved staged imports match the previously recorded output hashes. However, the runner does not separately rehash a preceding staged object immediately before and after its later import or retain compile-time resolution snapshots; between-stage mutation remains unobserved. Project/package transitive, historical source-object and dynamic ancestry remain inherited.

All four named captured axiom reports are exactly `[propext, Classical.choice, Quot.sound]` with empty stderr. The runner rejects coded diagnostics and `sorryAx` but does not enforce an exact named axiom whitelist; this review inspected the reports. Its terminal records `PASS` before its final assertion; the author reports outer exit 0, but no separately retained actual outer-exit receipt was found. Resource guards are sampled.
