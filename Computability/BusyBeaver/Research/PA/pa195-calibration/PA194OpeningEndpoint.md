# Model-length opening endpoint

`PA194MixedVector.mixed_shape` constructs and characterizes the internal substitution vector `[#0,…,#(k−1), &0,…,&(m−1)]` for arbitrary model lengths `k,m`. `PA194MixedTransition.mixed_transition` proves the vector equation for one opening, and `PA194FreeMixed.free_mixed_transition` lifts that equation to formula codes.

`PA194OpeningEndpoint.opening_history_endpoint` proves that every correctly constructed `n`-step Foundation opening history beginning at `qqAlls p n` ends exactly at `subst (fvarVec n) p`, provided `p` is internally well formed at bound depth `n` and shift fixes `p`. This works for arbitrary IΣ₁ arithmetic models, including nonstandard `p` and `n`.

`induction_body_of_closure` composes this equality with the earlier model-length induction-axiom theorem. It proves internal PA provability of the induction body `indBodyVal K`, provided an internally well-formed shift-fixed closure body `p` and length `n` satisfy `bv p = n` and `subst (fvarVec n) p = indBodyVal K`, and K is internally well formed. The earlier final-history equality assumption is discharged.

The construction of such closure bodies for every internal K remains open. This package does not establish arbitrary-formula PA induction, bounded comprehension, the distinct-label gate, an iPRA implication, or the machine consistency equivalence.

The author replay ran `check-opening-endpoint.sh` against the pinned Foundation overlay, rebuilding twelve local modules. Printed axioms contain only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
