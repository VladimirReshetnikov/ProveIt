# Adjacent-Pell step: reduced numerator, integrality and norm identity

This exploratory Lean packet checks three ingredients for the rational adjacent-Pell descent used by the ten-positive 80/81/83/84-operation proposals. Let `B=Q-1`, `m>0`, and consider the transformed signed numerator

`r'=(1+2*B)*r - 2*(1+B)*m*v`.

For any IΣ₁ model with the repository's ordered-ring interface, `adjacent_step_reduced_square` proves `Bez |r'| m 1` from `Bez r m 1` and `m²∣B`. The signed expression is represented by the magnitude of its two natural sides. Thus the transformed numerator remains coprime to the unchanged denominator, even when its sign changes. The separate [`AdjacentDenominator`](../ten-positive-adjacent-descent-prototype/README.md) module derives the required `m²∣B` from a reduced cross-multiplied norm; this packet does not yet compile a join of those statements.

Under `B=m²*t`, `adjacent_first_coordinate` proves that the magnitude of the other transformed numerator `(1+2*B)*m*v - 2*B*r` is exactly `m` times the magnitude of the explicit model pair `((1+2*B)*v, 2*m*t*r)`. This supplies integrality of its absolute quotient. Separately, `adjacent_norm_identity` proves the polynomial norm-preservation identity over any commutative ring for the two transformed numerators. No graph, sign or positivity hypothesis is used in that ring identity.

These are still **components**, not a complete model descent. The strict decrease of the first coordinate, exclusion of zero, integration of the sign-reflected pair with the norm and an internal least-number argument remain open. The module does not prove `m=1`, the auxiliary Pell quotient, a graph-to-machine theorem, an iPRA endpoint, or an external file binding.

Author attempt 04 exited 0 without warnings or `sorryAx`; its source snapshot, command, hashes and sampled resources are retained under `observations/attempt04/`. Source SHA-256 is `b8e30924e7e6fc236477a16f6c0c70fc1522977f909f8afad88f66bca52b7ce2`; object SHA-256 is `bf2cef6fd83385d21a3553ca2a774273bf9b8febb0c6dedae2ef40c5e8e2e2e2`. The four printed model-theorem axiom reports are `[propext, Classical.choice, Quot.sound]`; the generic commutative-ring identity reports `[propext, Quot.sound]`. Attempt 01 checked the reducedness result, attempt 02 added the square-divisibility corollary, and attempt 03 failed on parenthesization of two `calc` steps; all snapshots and logs are retained.

The bounded runner pins the abstract product-root, doubling and scaled-square objects plus selected `ArithmeticGcdNormalization`, source, runner and Lean binary before and after. The direct `ArithmeticAdaptiveFirstDivisibility2011` object and full project union are inherited, as are package-transitive, dynamic and complete historical source-to-object ancestry; no independent rebuild or paired replay is claimed. Resource observations are point samples, and temporary providers and objects may disappear.

From the repository root, with those providers present and a free guarded Lean slot, use `ATTEMPT=attempt05 python3 -I -S -B Computability/DiophantineConsistency/research/ten-positive-adjacent-preserve-prototype/run.py` for a fresh run.
