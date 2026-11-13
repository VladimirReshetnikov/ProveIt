# Explicit square-divisor witness

[`SquareDivisorWitness.lean`](SquareDivisorWitness.lean) proves two generic
commutative-ring identities. Given a Bézout certificate `a*x+b*y=1` and the
cleared norm `q*v²*b²=(q-1)*a²+b²`, Lean proves the explicit equation

```
q-1 = b² * ((q*v²-1)*(a*x³+3*b*x²*y)
                +(q-1)*(3*a*x*y²+b*y³)).
```

Thus the coefficient needed by the proposed integrality descent has a
polynomial divisor witness once those hypotheses are supplied. The proof
requires neither division nor integral-domain cancellation. It is valid for
arbitrary commutative rings, including rings with zero divisors.

This is an **external Lean theorem**, not an internal iPRA derivation and not
an IΣ₁-model transport. In particular it does not construct the graph's gcd
and Bézout witnesses, show that the signed quotient has a natural
nonnegative representative, prove descent termination or recover the ordinary
norm. The intended model represents signed coefficients by natural pairs;
applying this theorem to that representation and building the required
object-theory proof are separate obligations. A generic ring identity alone
does not prove the 12-variable equivalence.

## Bounded compilation observation

The Lean 4.32.0 binary from the local toolchain compiled the source in session
76535, with observed process exit 0. It used the historical package provider
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, removed
`LEAN_SRC_PATH`, `LEAN_SYSROOT`, `LD_LIBRARY_PATH`, `LD_PRELOAD` and `LD_AUDIT`
from the compiler environment, and printed:

```
'SquareDivisorWitness.square_bezout' depends on axioms: [propext]
'SquareDivisorWitness.norm_square_divisor' depends on axioms: [propext, Quot.sound]
```

The source SHA-256 was
`8eda221986355cf65a47354f3f22371cface6d62a8b7477ba9f43737467b62d7`,
the direct `Mathlib/Tactic/Ring.olean` input was
`cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4`,
and the Lean binary was
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
A separate `lean --deps` exited 0 and listed `Init.olean` (twice) and
`Mathlib/Tactic/Ring.olean` from that provider. The compilation also inherits
the provider's transitive and dynamic dependencies; it is not an independent
replay or a source-current closure build. The named Lean metatheory axioms
are not asserted as axioms of object-level iPRA.
