# Model-internal adjacent-Pell denominator descent

`denominator_one` proves in every IΣ₁ model with the repository's `ORingStructure` interface that `B>0`, `m>0`, `v>0`, `Bez r m 1`, and the cross-multiplied norm

`(1+B)*(m*v)² = m²+B*r²`

imply `m=1`. This is the reduced-denominator arithmetic theorem behind the rational adjacent-Pell step. Its positive numerator/coordinate and explicit Bézout-reducedness assumptions are part of the statement; it is not yet a theorem about a graph zero or a machine.

The proof makes the set of positive `w` admitting a reduced numerator for the same `B,m` a Σ₁-definable predicate, takes its model-internal least element, and uses the separately checked strictly decreasing step to force that element to be one. At one, the norm and `B>0` imply `m²=s²`; order makes `m=s`, and the Bézout certificate gives `m∣1`, hence `m=1`. This is an internal least-number argument in arbitrary models, not merely induction over standard external witnesses.

The theorem does not yet construct a reduced representation from the 80 graph's scaled equation, prove graph-to-machine equivalence or reverse witness existence, establish an internal iPRA proof, or bind the Lean graph to JSON/PDF bytes. Those remain separate tasks.

Author `observations/attempt02/` exited 0 with no warnings or `sorryAx`; the theorem's printed Lean metatheory axioms are `[propext, Classical.choice, Quot.sound]`. Source SHA-256 is `aae40ace48c04ba08198efe221b8eaf06a8d1c618c103b0cec533f40fff5db2c`; object SHA-256 is `e75ae912b24068b600e79d93eaef81e314146b7b50e0c4268c2f6db6fd0e650b`. Attempt 01 failed on ambiguous names and an unnecessary-simpa warning and is retained with its snapshot and log.

The guarded runner pins the adjacent-step and six predecessor objects plus selected `ArithmeticGcdNormalization`, source, runner and Lean binary. Other project imports, the rest of the provider, package-transitive and dynamic libraries, and full historical source-to-object ancestry remain inherited. Resource records are point samples, temporary objects may disappear, and no paired replay or independent audit is claimed.
