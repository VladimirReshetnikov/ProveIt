# Conditional free-J rank cancellation adapter

The Lean theorem composes two existing historical `IΣ₁`-model lemmas at
compact44 exponent **590069**, and may be paired with the separately proved
95-row free-J factor split. The two cancellation conclusions have explicit,
separate premises:

* From `0 < q`, `q³ ∣ Y`, and `q⁵ ∣ (3+4Y(X+1))t`, conclude `q⁴ ∣ t`.
  This uses `ArithmeticAdaptiveFactorThree2011.cancel_factor_three`, which
  permits `3 ∣ q`.
* From `q=(2^590069−1)J+1` and `q ∣ 3·2ᴿ`, conclude `q ∣ 2ᴿ`, using
  `ArithmeticAdaptiveMersenne2011.cancel_three`.

Here powers of two use the model's internal exponent function. `q, Y, X, t,
R, J` are separately quantified model elements: this prototype does **not**
identify them with the 95-row graph or show the compact44 port evaluates to
its displayed exponent in every model. Its combined theorem also assumes an
internal zero of that graph and returns the already established three factor
units, but does **not** derive either set of divisibility assumptions from
that split. In particular the second premise is a later rank consequence and
is not used to derive the early `q⁴` cancellation. Rank, norm recovery,
whole-tuple checker calibration, and the iPRA derivation are open.

Fresh replay session 98778 exited 0 and printed
`PASS_BOUNDED_CONDITIONAL_FREEJ_RANK_ADAPTER
955f79233a43e2500aa2f477a51bc097ad419604b2306e908ff9fd54236d2a06`.
The receipt records both axiom reports, source hashes, direct dependencies,
62-source declared historical closure, inherited fresh free-J replay, linked
object hashes and companion checks. The earlier exploratory session 16944
also exited 0. The replay is single-author and historical, not a matched full
project replay or an audit of dynamic or package-transitive dependencies.
