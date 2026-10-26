# Independent represented sequence-history review

Reviewer `/root/complemented47_review`, 26 October 2026. PASS within the
stated generic scope; no correction requested. This was a read-only
mathematical/source/provenance review. No compiler was invoked and no frozen
source or object was edited.

I read all 178 main lines and 47 check lines, the complete imported Foundation
PRF source, the relevant sequence append/lookup definitions and proofs, and
the complete old `ArithmeticHistory254` and `ArithmeticHistoryRecurrence254`
contracts for comparison. I also read the complete author receipt and all
three preparation/build/receipt scripts. I did not author this implementation;
my earlier C222 row/seed/checker reviews and HA arithmetic work are separate.

The key distinction is correct. `zeroDef`, `succDef`, `blueprint`,
`historyDef`, `historyDeltaDef`, `valueDef`, and `valueDeltaDef` are defined
before the ambient-model and semantic-step variables. They depend only on
`stepDef : Sigma1.Semisentence 3`. Foundation's blueprint graph is likewise
syntax-only; `graphDelta` is a fixed syntactic construction whose functional
interpretation is justified afterward. The `Fin 0` parameter vector is
identified with the unique empty vector, not instantiated with a hidden
model-dependent parameter.

The successor formula's three free slots are output, previous history, and
index. Its fresh existential value is supplied to `stepDef` as
`(value, previous, index+1)` and to `seqConsDef` as
`(output, previous, value)`. This agrees with `PR.Construction.succ`'s
index/previous argument order. The zero formula is the singleton sequence
`[0]`. The value graph existentially binds the same full history before
looking up the input code. I found no binder capture or off-by-one mismatch.

Both `history_total` and `value_total` explicitly use `include step hstep in`.
Their full interface retains a semantic `step : V → V → V` and an exact
`Sigma1-Function₂[V] step via stepDef` instance. Their proofs use that graph
instance to exhibit the concrete history/value and establish uniqueness.
They do not assert totality for an arbitrary supplied Sigma1 relation.
The two rejected drafts omitted those section parameters; the final source
correctly repairs the premise, and the focused checks supply it explicitly.

Sequence validity, length and lookup preservation use definable IΣ1
induction over `code : V`, not induction restricted to standard Nat values.
The lookup proof splits the appended index from an earlier index; sequence
membership and uniqueness preserve each older value. Outside length
`code+1`, the underlying total `znth` definition returns zero. Thus the API
includes every internal lookup, not only valid child indices. The HFS numeric
bound `value < history` follows from actual range membership, not an assumed
encoding-size inequality.

The packet imports only Foundation PRF and does not import or rename the old
fixed C254 evaluator. It reuses the primitive-recursion construction itself.
Although its shape matches the generic portion of History254, no old C254
semantic agreement, actual C222 row, seed validity, runtime translation,
closed arithmetic derivation of C222 totality, or HA equivalence is claimed.
Those remain distinct instantiation and calibration obligations.

Frozen sources under `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`:

| Source | SHA-256 |
|---|---|
| `ArithmeticSequenceHistory.lean` | `764b832d28249b17d640a7a3a2b3721deb90a0ee82360e48331be6dabd0d9a3d` |
| `ArithmeticSequenceHistoryChecks.lean` | `d7b4b09a3403dfcdd151a566ceb6332ccea8df36cd330922aa742e2302cc9aea` |

I independently rehashed all 95 selected Foundation sources, 380 listed
objects/companions, 37 explicit external objects, the parent receipt,
compiler, manifest, drivers, final source snapshots/objects/logs/timings,
and all executed development snapshots/logs/timings. I compared each selected
source's import list with the inventory and checked direct-import closure
against the selected set and explicit external boundary. Every pin matched.
The unexecuted planned checks after each failed main are correctly recorded
without an exit code; they are not counted as executions.

The author's final two capped builds exited zero, with an empty main log
and 15 reports containing only `propext`, `Classical.choice`, `Quot.sound`.
This authenticates the author's records; it is not an independent fresh
replay or a new Foundation-closure claim. Final objects are
`6fbbbe4bd63cdd7311ffc0c21f0209a34a831ceb460aa81171c2ce5207291db9`
and `715c0eaea7af5ee491ca0eccc57cbf6cd345440f3ac38817ab8284d322135a75`.

Author receipt SHA-256:
`459ec80ab2c61da090da9bdafa6a6a36f28816f47fdb2cb3114fb9357a44260f`.
Replay receipt SHA-256:
`c21618568efb69a1516ad30ae2d7ed833345785b8db803a71e8badac7016cd66`.
Input inventory SHA-256:
`178466663847772ae4480a7fff2d9c5feda836c4ea591a04d38c7a345e47919a`.
