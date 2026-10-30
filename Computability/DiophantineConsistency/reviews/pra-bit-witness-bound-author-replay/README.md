# Foundation bit graph: conditional witness binding

`PRABitWitnessBound.lenbit_in_bit_bound` applies the checked generic semantic
`bnd`/rewriting naturality theorem to the exact inlined `lenbitDef` occurrence
in Foundation's `bitDef`, retaining its `y+1` local majorant.
`bit_bnd_of_witness` then proves the actual bounded `bitDef` graph in every
IOpen model from a known witness `z ≤ y`, the original inlined lenbit graph,
a shared bound `w ≥ y+1`, and the **separately bounded inlined expDef graph**.
`candidate_proves_bitBoundSentence` is an actual candidate-PRA proof of the
universally closed conditional implication with those premises.

The bounded expDef conjunct is not supplied here. Binding this bit graph inside
the derivation fixpoint, bounding the sequence history and obtaining the full
refutation bound certificate also remain open. No IΣ₁ or Σ₁ collection is
assumed in candidate-PRA models.

The author build `/tmp/pra-bit-bound-vbhbthrm` passed both source/check modules
and final authentication. It uses the independently accepted 35-module local
provider graph plus separately replayed `PRABndRewriting` and
`PRALenbitWitnessBound` providers. `inputs.json` pins that graph, the two
focused source/object pairs and the Foundation HFS Basic, Exponential Bit,
Exponential Pow2, IOpen Basic and PeanoMinus Functions source/object pairs.
Foundation, Mathlib and other transitive package dependencies remain inherited;
hashing the selected Foundation files does not authenticate their full source
closure. Source snapshots, complete logs, terminal state and exact commands
are retained in `author/`. The axiom checks report only `propext`,
`Classical.choice` and `Quot.sound`.

For independent replay run:

```sh
python Computability/DiophantineConsistency/reviews/pra-bit-witness-bound-author-replay/replay.py \
  --parent /tmp/pra-bnd-rewriting-independent-7n8kd56j/lib \
  --lenbit /tmp/pra-lenbit-bound-9nnf4u_8/lib \
  --expected Computability/DiophantineConsistency/reviews/pra-bit-witness-bound-author-replay/author/state.json
```

The driver checks PASS parent states, the 35-module recorded local source/object
graph, focused naturality and lenbit source/object pairs, the stated Foundation
pairs and both client sources before and after; it compares client source,
object and full-log hashes against the author.

Both independent replays passed: root `/tmp/pra-bit-bound-2wp5u9vz` and
private `/tmp/pra-bit-bound-4_hh25s2`, with matching source, object and full-log
hashes for both modules. Their snapshots, logs and terminal states are retained
in `root/` and `private/`.
