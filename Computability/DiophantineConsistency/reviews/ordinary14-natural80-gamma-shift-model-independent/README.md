# Independent source review: natural-80 to natural-81 gamma shift

The [gamma-shift draft](../../research/ordinary14-natural80-gamma-shift-model-draft/README.md) states the correct changed-valuation relationship and the intended existential directions, conditional on its unelaborated gamma-positivity client. The original and independent receipts reproduce. This is an external graph and source-signature review, not Lean elaboration or a model theorem.

The independent checker compares all 80 and 81 literal graph rows, the 14 input/4 port aliases and output-factor selections to their pinned JSON graphs. It verifies that the only graph edit deletes `gamma=n_gamma+1` and substitutes `n_gamma` at each consumer. Consequently the 80 graph at a ring valuation `v` equals the 81 graph at the valuation whose slot 12 is `v 12-1`, for arbitrary commutative rings and signed integer ports. The checker also verifies the exact one-coordinate cancellation `(v 12-1)+1=v 12` structurally, rather than relying on finite evaluations.

For the intended natural-model transport, `Related v80 v81` says `v80 12=v81 12+1` and equality at every other slot. The proposed related-valuation embedding and `ModelDifferenceRing.internalZero_iff` give both `InternalZero` directions at those **related** inputs. In the 80-to-81 existential direction, the source calls the separately proposed gamma-positivity theorem, obtains a predecessor and substitutes it in slot 12. The proof now explicitly uses `add_comm` when converting the `exists_add_of_le` witness `1+g` to the required `g+1`. In the reverse direction it increments the 81 gamma coordinate and applies the reverse implication. No pointwise same-valuation identity is claimed.

The existential source theorem explicitly requires all four represented ports, `beta>0`, `K0>0`, `MC<beta` and `MF<2*beta`; it has no positive-gamma premise. Those are precisely the source-level arguments supplied to the unelaborated positivity client. Its existence conclusion remains conditional on successfully elaborating that client and every imported graph/model lemma. The source's `simp`, `fin_cases`, predecessor extraction, ring embedding and rewrites have not been checked by Lean. The three `#print axioms` commands have not run, and this packet does not prove an iPRA derivation, provider/axiom closure, or a physical coefficient/PDF binding.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-shift-model-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-shift-model-independent/result.json
```
