# Negative sqrt/lenbit existential

This proof bounds the exact negative existential `“x m. ¬∃ s <⁺ x, !sqrtDef s x ∧ s*s = x ∧ !lenbitDef s m”` occurring in Foundation's `sppow2Def`. In every IOpen model, the formula implies its bounded translation at `m+1`, with no restriction on `x`; the proof uses the open sqrt graph and the negative lenbit local bound. Candidate PRA proves the universally closed bound sentence.

This handles a reverse-iff subformula and does not establish the full `sppow2Def`, `ppow2Def`, `exponentialDef`, `bitDef`, fixpoint or ρ bound, or the HA equivalence.

The replay authenticates the refreshed local parent graph, the directly imported negative lenbit modules and selected Foundation source/object pairs, including `PPow2` and `Pow2`. Other Foundation and Mathlib transitive dependencies are inherited rather than source rebuilt.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-negsqrtlenbit-bound-author-replay/replay.py --parent /tmp/pra-neglenbit-pow2-bound-2zwfsc4r/lib --expected Computability/DiophantineConsistency/reviews/pra-negsqrtlenbit-bound-author-replay/author/state.json
```
