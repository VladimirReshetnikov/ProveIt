# Adjacent-Pell integral quotient from a scaled norm

`quotient_of_scaled_norm` proves in every IΣ₁ model with the repository's `ORingStructure` interface that `B>0`, `M>0`, `v>0` and

`(1+B)*(M*v)²=M²+B*z²`

imply the existence of a model element `y` with `z=M*y` and `(1+B)*v²=1+B*y²`. Neither scale divisibility nor a Bézout-reduced fraction is assumed. The proof constructs the internal gcd of `z` and `M`, obtains the reduced numerator/denominator and its signed Bézout certificate, cancels the positive gcd square from the norm, and invokes the separately checked [least-number adjacent descent](../ten-positive-adjacent-complete-prototype/README.md), which forces the reduced denominator to one.

This is an abstract model theorem. It does not itself derive the hypotheses from the actual 80-row graph, establish the sign and positivity of its adjacent root, prove graph-to-halt equivalence, or show an iPRA derivation. Those are separate joins and proof obligations.

Guarded author `observations/attempt01/` exited 0 without warnings or `sorryAx`; its printed Lean metatheory axiom report is `[propext, Classical.choice, Quot.sound]`. Source SHA-256 is `1a2c56384ec3c3d9d93ca448870be05cc3f742b684ef3800e35ecbe6d024c063`; object SHA-256 is `19321c96c92462072fc3fe6cf30212535baa29e7915e1e59ca2c26073873dc34`. The runner pins the descent and seven predecessor objects, selected `ArithmeticGcdNormalization`, source, runner and Lean binary before and after. Other direct imports, the remaining selected provider, package-transitive and dynamic dependencies, and complete historical source-to-object ancestry are inherited. Resource samples are not continuous, temporary objects may disappear, and this is not a paired replay or independent audit.
