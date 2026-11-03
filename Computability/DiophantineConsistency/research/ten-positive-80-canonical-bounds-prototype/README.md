# Canonical rank and cubic-divisibility bounds

`TenPositive80CanonicalBounds.rank_gt_three_radix` proves `3*q < rankNat`
in every stated IΣ₁ model from beta at least 31 and positivity of J, alpha
and w. It does not require a graph-zero premise, fixed symbolic ports, or
the other positive variables. The proof bounds q below by 32, bounds the
rank below by `q*q-1` using positive alpha, and compares that to `3*q`.
`cubic_divides_ordinate` proves `q^3 ∣ Y` directly from the definition
`Y=q*q*q*s`, with no positivity or zero premise. These are two conditions
used by the canonical source reconstruction; neither constructs its
witnesses or establishes graph equivalence.

The guarded author check `observations/attempt03/` passed and
reported only `propext`, `Classical.choice`, and `Quot.sound` as Lean
metatheory dependencies. Its object is
`/tmp/tenpositive-80canonical-bounds-1hl2di9j/Direct80CanonicalBounds.olean`,
SHA-256 `8a3ec759c6a61a1fa23ee9bfaab24ffe98adf968e6ff919c60e17844ee7eacea`.
Attempts 01 and 02 retain elaboration errors and are not evidence of a
successful check. The runner pins selected inputs and resource samples;
transitive project/package and dynamic ancestry and historical source-object
provenance are inherited, and this is not an independent Lean replay.
