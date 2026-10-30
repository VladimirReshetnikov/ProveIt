# Foundation Seqₛ graph bound

`PRASeqSWitnessBound` proves that Foundation's exact `Exponential.Seqₛ.def` graph at `(y,X,Y)` entails its bounded translation at `X+Y+2*y+1` in every IOpen model. It binds the negative ppow2 branch and all eight ext substitutions inside the actual bounded universal. The module also proves the conditional version for any common `w` above `X+1`, `Y+1`, and `2*y+1`, and derives both corresponding universally closed candidate-PRA sentences.

The full exponential graph, bit membership, the fixpoint, ρ, and the target HA equivalence remain open.

The replay authenticates the source-current local parent graph, direct negative ppow2 and sppow2 dependencies, selected Foundation source/object anchors, and the parent terminal state. Other Foundation and Mathlib transitive dependencies are inherited rather than rebuilt from source. The initial author run rejected a linter warning; its receipt and source are preserved in `failed_author/`, and the corrected source has an empty diagnostic log.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-seqs-witness-bound-author-replay/replay.py --parent /tmp/pra-negppow2-witness-bound-g0ca_hqp/lib --expected Computability/DiophantineConsistency/reviews/pra-seqs-witness-bound-author-replay/author/state.json
```
