import IntegerPoints.IwaniecMozzochiEq73Conclusion
import IntegerPoints.IwaniecMozzochiPoissonEq72

/-!
# Iwaniec--Mozzochi (7.5): unconditional conclusion

The analytic estimates (7.3)/(7.4) are proved in
`IwaniecMozzochiEq73Conclusion`, while `IwaniecMozzochiPoissonEq72` proves the
Poisson-summation identity (7.2).  This module combines exactly those inputs
through the Section 7 reduction, without importing the unrelated later
premise-reduction chain.
-/

namespace LeanProofs.IntegerPoints

/-- **Iwaniec--Mozzochi (7.5).**  The long-Farey-cell bound follows
unconditionally from the proved Poisson identity (7.2) and the proved
oscillatory-integral estimates (7.3)/(7.4). -/
theorem iwaniecMozzochi_eq75_holds : iwaniecMozzochi_eq75 :=
  iwaniecMozzochi_eq75_of_eq72_eq73_eq74
    iwaniecMozzochi_eq72_holds iwaniecMozzochi_eq73_eq74_holds

end LeanProofs.IntegerPoints
