# Adjacent-Pell denominator prerequisite

This small author-checked module proves a necessary first step toward the rational adjacent-Pell descent used by the ten-positive 80/81/83/84-operation equations. It works in every IΣ₁ model with the repository's `ORingStructure` interface.

`bez_right_square` derives `Bez r (m*m) 1` from the explicit natural signed Bézout certificate `Bez r m 1`. `denominator_square_divides` assumes `m>0`, that certificate, and the cross-multiplied relation

`Q*(m*v)² = m²+B*r²`.

It proves `m² ∣ B`. In the intended adjacent-Pell application `B=Q-1` and `r/m` is reduced; the theorem itself does not assume or prove that specialization. It uses the internal gcd and unit-cancellation infrastructure rather than standardness or prime factorization.

This does **not** prove the descent step, preservation of a reduced denominator, termination, `m=1`, integrality of the second Pell root, graph-to-machine equivalence, or iPRA derivability. It also does not bind the graph or file data. Those remain separate obligations.

The clean author attempt 04 exited 0 with no warnings or `sorryAx`; source and complete logs are retained in `observations/attempt04/`. Both printed axiom reports are `[propext, Classical.choice, Quot.sound]` in Lean's metatheory. Source SHA-256 is `c1185203a799377e5ba757caca402c53f3eee9624ae6cc00f786afe931efecf3`; object SHA-256 is `83c7300a38a6d5619d9802679be749fbe8088a1be0e34c3683aecd7965dc9ff9`. Attempts 01–03 failed respectively on an absent module path, an unsuitable ring `dvd_sub` lemma for model truncated subtraction, and a reversed remainder equality; their source snapshots and error logs are retained.

The guarded runner pins the doubled and scaled-square prototype objects and the selected `ArithmeticGcdNormalization` object, source, runner and Lean binary before and after. It inherits the selected 90-operation project union, its other direct imports, package-transitive and dynamic dependencies, and complete historical source-to-object ancestry without independently rebuilding or hashing them. Resource observations are sampled, not continuous, and `/tmp` objects may disappear. This is not a paired replay or an independent review.

With the recorded provider present and a free guarded Lean slot, rerun from the repository root with a fresh name: `ATTEMPT=attempt05 python3 -I -S -B Computability/DiophantineConsistency/research/ten-positive-adjacent-descent-prototype/run.py`.
