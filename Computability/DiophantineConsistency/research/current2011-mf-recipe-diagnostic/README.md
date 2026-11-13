# Isolated current2011 high-mask recipe identities

This is a diagnostic toward the MF byte binding, not the complete binding.
The [source](CurrentMFRecipe.lean) checks that the explicit radix is the
current2011 radix, the explicit 2,011-digit list is the current high-mask
list, that its radix decoding is `highPort`, and that `rho^2011 - 1` is beta.
The three printed axiom reports for the digit-list, high-port, and beta
identities contain only `propext`.

Observed outer session 2777 exited 0; dependency and compile commands exited
0, the Lean compile took 2.12 seconds, and its log has no warning, error, or
`sorryAx`. The direct-input guard, inherited current14 base and preflight
limits are recorded in [attempt01](attempt01/). The temporary object
`/tmp/current2011-mf-recipe-diagnostic-20261105/CurrentMFRecipe.olean` has
SHA-256 `640e409a33982e2cad2fa9c1135c12f3151aae797674fcd0cdedeb481d0ca3a0`.
This result does not yet prove the once-beta-shifted fourth port, a byte
decoding result, file semantics, or a new iPRA theorem.
