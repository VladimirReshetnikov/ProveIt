# Symbolic fixed beta exceeds the height threshold

`Direct80FixedBetaLower.beta_ge_31` proves in every IΣ₁ model that the symbolic `CompactFixedBeta.betaNat` is at least 31. It uses the existing symbolic Mersenne identity and monotonicity of represented exponentiation; it does not evaluate or expand the 590,069-bit fixed numeral.

Guarded author `observations/attempt01/` passed without diagnostics, yielding `/tmp/tenpositive-fixed-beta-lower-7ihtslwr/Direct80FixedBetaLower.olean`, SHA-256 `370a71e627298247c5f236b002a7afa820063c344743937c2369dc48724b3801`. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. The selected `CompactFixedBeta` object, other selected prototype objects, and one inherited provider are pinned; complete transitive project/package/dynamic and historical source-object ancestry remain inherited. Resource checks are sampled; no paired replay is claimed.

This only proves the lower bound for the named symbolic fixed beta; binding it, the other ports, the final machine theorem, and iPRA endpoint require separate joins.
