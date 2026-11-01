# Fourteen-variable square-witness model replay

The author and peer each compiled the frozen 14-variable model proof and its
axiom checks on separate overlays of the same matched 13-variable model peer.
The actual `replay_model.py` session `39270` exited zero with
`MATCHED_PASS 2 rows`. The receipt records matching source, object, log and
direct-input hashes, with 50 selected direct dependency and companion paths
(including absence) guarded in each run. The four axiom reports contain no
axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

This is a focused same-provider replay. It inherits the transitive project,
package and dynamic ancestry of its parent; the recorded source checks are not
a full current-source closure. It verifies the model-level zero-set transfer,
not an intuitionistic PRA derivation of the consistency equivalence.
