import DiophantineConsistency.OnePageDisplay54

open DiophantineConsistency
open OnePageDisplay54

namespace OnePageDisplay54Checks

set_option maxRecDepth 10000

example (r : ℕ) (hr : r ≠ 0) : displayedK r = (NativeStencil54.rawWord r : ℚ) :=
  displayedK_eq r hr

example : displayedMC NativeStencil54.radix = (NativeLowPort54.lowPort : ℚ) :=
  displayedMC_eq

example : displayedMF NativeStencil54.radix =
    ((NativeStencil54.radix^NativeStencil54.cellLength-1+
      NativeHighPort54.highPort NativeStencil54.radix : ℕ) : ℚ) := displayedMF_source

example (m : ℕ) {x : ℚ} (hx : x ≠ 1) : G m x = (x^m-1)/(x-1) :=
  geometric_fraction m hx

#print axioms geometric_fraction
#print axioms target_factor
#print axioms auxiliaryPhi_eq
#print axioms displayedK_eq
#print axioms displayPositions_perm
#print axioms support_eq
#print axioms support_recipe
#print axioms displayedMC_eq
#print axioms mu_eq
#print axioms displayedMF_eq
#print axioms displayedBeta_eq
#print axioms displayedMF_source_eq
#print axioms displayedMF_source

end OnePageDisplay54Checks
