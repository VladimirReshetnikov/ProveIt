# Shifted-guard model arithmetic: fact-level source draft

This is an **uncompiled source proposal**, not a Lean theorem or a graph-to-endpoint proof. The propositions are stated for an arbitrary `ORingStructure` model of IΣ₁; each assumes the explicit natural magnitude, balance, and positivity facts it uses. No transport sign, old first-root coordinate, or external standard-integer argument is silently imported.

* `oriented_scaled_pair` proposes that, when a natural signed pair has positive difference and its magnitude squared is `scale² * radicand`, the existing internal scaled quotient gives a positive natural root and an oriented pair. Both `scale` and `radicand` must be positive. This uses `ArithmeticAdaptiveQuotients2011.scaled_quotient` and `ArithmeticSignedPairs.magnitude_of_add`.
* `sign_free_main_quotient` supplies the explicit dominance premise using `ArithmeticAdaptiveMainOrientation2011.main_parts_positive`, provided `U > 0`, `Y ≥ 8`, and `k > 0`. Its norm identity and positive radicand are assumptions, not consequences established here.
* `q4_rank_from_balance` follows `ArithmeticAdaptiveRankCongruence2011.rank_congruence_of_main` at the level of a displayed balance. It uses `ArithmeticAdaptiveFirstDivisibility2011.dvd_magnitude_of_mod`, `magnitude_mod`, and `ArithmeticAdaptiveFactorThree2011.cancel_factor_three`. In particular cancellation covers the case `3 | q`; it assumes `q > 0`, `q³ | Y`, and the entire displayed balance.

`scaled_quotient` itself relies on the internal square-divisibility result `ArithmeticSquareDivisibility.dvd_of_square_dvd`. These sources describe model-level mathematics; source presence or copying a proof does not certify this draft's elaboration or its provider ancestry.

A graph-specific client must still establish the actual signed-pair and scaled norm identities, positive radicand, `Y ≥ 8`, `q³ | Y`, and the balanced equality from the 87 graph. It must also instantiate every hypothesis of `P72Exact.indices_ordinary` with the correct witnesses (`μ = q⁴`, `i′ = i`), construct the growth/finish route and port bounds internally, and prove the remaining witness and endpoint bridges. The external standard-integer calibration cannot simply be applied to an arbitrary model. No new claim is made about graph zeros, halting, iPRA, TeX, PDF, or file semantics.

`check_source.py` is a bounded source/pin check only; it does not invoke Lean, typecheck proofs, verify provider objects, or replace independent mathematical review.

Independent source and mathematical review is recorded in
`../../reviews/ordinary14-shifted-guard87-fact-lemmas-draft-independent/`.
