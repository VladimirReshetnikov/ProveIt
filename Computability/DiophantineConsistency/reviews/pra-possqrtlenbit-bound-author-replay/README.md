# Positive sqrt/lenbit existential

This proof bounds the exact positive existential `“x m. ∃ s <⁺ x, !sqrtDef s x ∧ s*s = x ∧ !lenbitDef s m”` occurring in Foundation's `sppow2Def`. In every IOpen model, given `x ≤ m`, the formula implies its bounded translation at `m+1`. Candidate PRA proves the universally closed conditional sentence; the explicit inequality reflects the surrounding bounded universal.

This handles a forward-iff subformula and does not establish the full `sppow2Def`, `ppow2Def`, `exponentialDef`, `bitDef`, fixpoint or ρ bound, or the HA equivalence.

The replay authenticates the refreshed local parent graph and selected Foundation source/object pairs including `PPow2` and `Pow2`. Other Foundation and Mathlib transitive dependencies are inherited rather than source rebuilt.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-possqrtlenbit-bound-author-replay/replay.py --parent /tmp/pra-after-three-induction-independent-1k0vgmf2/lib --expected Computability/DiophantineConsistency/reviews/pra-possqrtlenbit-bound-author-replay/author/state.json
```
