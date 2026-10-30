# Foundation exponentialDef positive graph bound

`PRAExponentialWitnessBound` proves that Foundation's exact positive `exponentialDef` graph at `(x,y)` entails its bounded translation at `(y⁴+1)+(y²+1)+(2*y²+1)+(y⁴+y⁴+2*y+1)` in every IOpen model. It binds both initial and final ext graphs, Seqₛ, and positive ppow2 inside the exact formula. Candidate PRA proves the universally closed bound sentence; no bounded collection or IΣ₁ assumption is used.

The author and two independent peer replays verify a pre-merge snapshot. Both peers use the frozen, hash-verified source tree at the path in `frozen-source-location.txt`; a separate current-source 67-module refresh is running. The immediate Seqₛ and positive ppow2 providers, their local graph, selected Foundation source/object anchors, and provider states are authenticated; other Foundation and Mathlib transitive dependencies are inherited rather than rebuilt.

The swapped `expDef`, bit membership, fixpoint, ρ, and target HA equivalence are not established by this packet.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-exponential-witness-bound-author-replay/historical-replay.py --parent /tmp/pra-seqs-witness-bound-x8706f04/lib --expected Computability/DiophantineConsistency/reviews/pra-exponential-witness-bound-author-replay/author/state.json --source-dir /tmp/pra-exponential-frozen-root-zfpljryz/Computability/DiophantineConsistency/Lean/DiophantineConsistency --lean-root /tmp/pra-exponential-frozen-root-zfpljryz
```
