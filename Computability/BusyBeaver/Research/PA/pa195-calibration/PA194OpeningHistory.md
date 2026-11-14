# Internal universal-opening history

`PA194OpeningHistory.opening_history` constructs, in any model of IΣ₁ and for any starting code `x` and model length `n`, a Foundation sequence with `n+1` entries, beginning at `x` and repeatedly applying the concrete operation `opener p = free (sndIdx p)`. `sndIdx` decodes the body when its input is a universal code. This uses Foundation's IΣ₁ primitive-recursion sequence construction and applies to nonstandard lengths and codes.

`opening_history_exists_sound` combines this construction with the model-length internal-PA soundness induction: when `x` is internally PA-provable, the constructed history is provable at every entry provided that each entry to be opened is certified to be a universal formula with an internally well-formed body. This is an explicit hypothesis, not established for a given induction axiom.

The package does not prove that the intermediate entries of a particular `qqAlls` axiom have the necessary universal shape, identify the endpoint with `subst (fvarVec m) b`, construct induction-axiom recognizer witnesses, prove comprehension, discharge the distinct-label gate, or establish an iPRA implication.

The author replay ran `check-opening-history.sh`, rebuilding both modules against the pinned Foundation overlay. The printed axioms are `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` appears.
An independent complete replay of the same script also passed without `sorryAx`.
