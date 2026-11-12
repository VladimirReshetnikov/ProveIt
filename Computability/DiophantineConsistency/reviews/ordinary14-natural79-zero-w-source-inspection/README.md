# Source inspection of the natural-79 zero-w divisibility chain

No grounded source-level inconsistency was identified in this bounded manual
inspection, so no patch is proposed. This is not a Lean check: parsing,
implicit arguments, instance and tactic resolution, reduction and theorem
bodies are not verified. Nor is the observation an exhaustive mathematical
review or an iPRA proof.

The inspected corrected overlay is pinned by SHA-256 below. The residue-shape
and concrete-unit clients connect the three residue exclusions to the five
units with `w = 0`. The J-positivity client additionally assumes a represented
K port; the zero-w main-norm client uses a represented beta and requires
positive beta and J only for its signed scaled quotient. The root cut keeps
both signs of that quotient, requires no representation of the remaining
ports, and derives `(4Y+3) ∣ 3q²`. The final client additionally carries the
K representation, establishes `q ≥ 2` and `Y ≥ q³`, reflects divisibility to
the model, and uses the positive dividend to invoke `Arithmetic.le_of_dvd`.
The Foundation import is explicit in the corrected reflection helper.

The main ring steps were checked against their selected statements: from
`D=U*Y*C+H*shift` and `D=U*d`, the cut obtains `H ∣ U*(d-Y*C)`; the norm
`d²=1+(Y²+H)C²` gives `H ∣ U`; and `H=4Y+3`, `U=Yq²` gives `H ∣ 3q²`.
The final strict size inequality follows from the explicit bounds. These
checks do not show the Lean tactics actually establish those statements.

Source snapshots (relative to the corrected overlay's `source/` directory):

```text
2570ae56ca0c4081b9442d768d94a4ded2cb365b74ed66bfe040c202b65aec1c  Natural79ZeroWUnits.lean.src
b4d60c7db8fb92cac53f38f81414a6319d8979ccbcb575d2e29e49fa5a51fd38  Natural79ResidueShapes.lean.src
253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d  Natural79ConcreteUnits.lean.src
f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a  Natural79ZeroWJPos.lean.src
afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009  Natural79ZeroWMainNorm.lean.src
c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec  Natural79ZeroWRootCut.lean.src
4ab36ba289a4cfce93d80bcc6bcb2cc75f0ca2a64d0a729b076846775dac0896  Natural79ZeroWDivisibility.lean.src
90acd025abeaf3e687a28e1e4d2c8695f8443340848430419e3057c4c7ff33f4  NaturalDvdReflectionSlim.lean.src
111f5a6da543baf6f08b3b1c6e5e8371cfb222197ba4566b8693598edffb6833  ForcedWDivisibility.lean.src
5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36  P79NaturalForcedW.lean.src
```

The provider source declarations `natural_magnitude_square`,
`scaled_quotient`, `product5_positive`, `negative_residue`,
`evalSemiring_map` and `split_evalRing` were also inspected, but their current
source bytes are not an authentication of any compiled provider. No Lean or
staging was performed.
