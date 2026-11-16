# Conditional internal induction-axiom endpoint

For any IΣ₁ arithmetic model and arbitrary internal formula code `K`, `PA194InductionEndpoint.induction_body_model_length` constructs Foundation's actual `InductionUnivR` witness and an internal PA proof of `indBodyVal K`, assuming a body `p` and model length `n` with all of the following properties: `p` is well formed at bound depth `n`, shift fixes `p`, `bv p = n`, and substitution by `fvarVec n` yields `indBodyVal K`. The theorem also explicitly assumes that any correctly constructed n-step universal-opening history has final code `subst (fvarVec n) p`. It uses the independently checked model-length history and universal-shape proofs. The assumptions and `K`, `p`, `n` may be nonstandard.

`induction_body_one` establishes the case `n = 1` without assuming the final-history equality: direct specialization and shift-fixity identify the endpoint. It still assumes the corresponding closure body and its exact recognizer decoding properties. `axiom_ind` proves internal PA provability from a well-formed recognized induction axiom.

The model-length final-code equality and existence of suitable closure bodies remain open. Thus this package does not prove arbitrary-formula PA induction, bounded comprehension, the distinct-label gate, or an iPRA implication.

The author replay ran `check-induction-endpoint.sh`, rebuilding the six local modules against the pinned Foundation overlay. Printed axioms are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
