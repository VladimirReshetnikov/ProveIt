# Actual exp, bit, and derivation fixpoint bounds

`PRAExpWitnessBound` transports the full positive exponential graph bound to Foundation's actual swapped `expDef`. `PRABitFullWitnessBound` proves the actual positive `bitDef` graph at `(x,y)` implies its bounded translation at `exponentialMajorant(y)+y+1`; it establishes monotonicity of the explicit polynomial and discharges the previously conditional bounded-exp premise. Both results have universally closed candidate-PRA derivations.

`PRAFixBitDerivationBound` binds the positive bit graph into Foundation's exact `derivation T` fixpoint. It proves, including as a closed candidate-PRA sentence, that a witness `s<w`, a shared bound above the bit polynomial, the original `bitDef(d,s)` graph, and the **separately bounded actual `limSeqDef` conjunct** imply the bounded derivation graph. That limSeqDef premise is not supplied here. The full refutation bound certificate and HA equivalence remain open.

The replay authenticates the post-merge 67-module local parent graph, selected Foundation source/object anchors including exponential, bit, and bootstrapping proof syntax, and the parent terminal state. The parent has an author receipt; its independent graph peers are running separately. Other Foundation and Mathlib transitive dependencies are inherited rather than rebuilt from source.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-exp-bit-fix-bound-author-replay/replay.py --parent /tmp/pra-after-strict-bridge-refresh-w4cezxfl/lib --expected Computability/DiophantineConsistency/reviews/pra-exp-bit-fix-bound-author-replay/author/state.json
```
