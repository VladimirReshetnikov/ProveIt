# Independent review: trace75 signed offset estimate

For any `ORingStructure V` model of IΣ₁, the accepted `Trace75OffsetBound.graph_offset_bound` assumes arbitrary natural ports `p` with **positive** beta cast `0<(p 0 : V)` and an all-positive `v : Fin 10 → V`. It has **no graph-zero hypothesis** and no assumed transport-sign hypothesis. It proves, in the model's difference ring, the strict inequality

```
2 * (actual trace75 e register) < (actual V register)² * (actual D register),
```

where the actual `D` register is `X*Y`. This is distinct from the source's local abbreviation `D := delta p v`. The proof uses actual signed `e=k−rank−1`, `B=c*T−rank` and **unsquared** `V=F*B−c`, with `F=1+2*delta*U²*E`. It derives `e<B`, `c+1<F` and `2≤X*Y` from the explicit positive inputs, then invokes the generic ordered-ring `offset_bound`, supplying the difference ring's discrete-order property. The result is not itself a proof that B≥0 or the old mask coordinate is positive, a trace74 guard, halt/iPRA equivalence, or an internal JSON/payload binding.

`check.py` rehashes source/copies, runner, Lean binary, recorded pins, output and logs; resolves direct and selected inherited providers; and verifies the earlier failed attempt. Its direct `OffsetBound` provider and selected `CarrierTransport`/`TransportOrder` objects come from the reviewed **fresh generic rebuild**; direct `Trace75Residue` is the reviewed symbolic graph provider. Their exact hashes and paths are in `check-output.txt`. The earlier generic rebuild removed a direct 80 import but did not separately rehash its staged prior objects around later imports; neither a full transitive 80-exclusion nor a complete historical/project/package/dynamic provenance audit follows.

Accepted attempt02 has object `ff61154c7dfec50724c92d55a95b3610d41bccb8c294b02b0a888ef4db11236b`, inner exit 0, empty stderr and sole named report exactly `[propext, Classical.choice, Quot.sound]`. Attempt01 had nonzero Lean exit for a missing historical `Direct80RankEquality` module and is not accepted. The runner rejects coded warnings/errors and `sorryAx` but does not enforce a named axiom whitelist; the report was independently inspected. Its terminal precedes final assertions and no separately retained actual outer-exit receipt was found. No Lean replay was performed.
