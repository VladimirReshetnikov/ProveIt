/-!
Uncompiled adapter to the vendored grh-lean interface.
This is NOT a formalization of prime-labelled codes.
Run in the separate grh Lake package after building the pinned dependencies.
-/
import Main

namespace PrimeCodeInput

theorem halfPlane : DirichletLNonvanishingRightOfHalf :=
  LFunction_ne_zero_of_half_lt_re

theorem criticalStrip : DirichletLZerosOnLine :=
  LFunction_eq_zero_re

theorem primitiveCriticalStrip : PrimitiveDirichletLZerosOnLine :=
  LFunction_eq_zero_re_of_isPrimitive

end PrimeCodeInput

#print axioms PrimeCodeInput.halfPlane
#print axioms PrimeCodeInput.criticalStrip
#print axioms PrimeCodeInput.primitiveCriticalStrip
