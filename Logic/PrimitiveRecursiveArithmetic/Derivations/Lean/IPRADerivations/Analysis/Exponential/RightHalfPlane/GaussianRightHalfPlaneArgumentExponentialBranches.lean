import IPRADerivations.Analysis.Exponential.RightHalfPlane.GaussianRightHalfPlaneArgumentExponential

/-!
# Exponential readback after both numerical argument selections

The original exponential of the selected argument agrees with the
actual branch exponential even when both programs use different
radii. The signed branch uses conjugation of the unsigned exponential.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentExponentialBranches

open_ipra
open GaussianArctangentCayleyValues (imaginaryPoint)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianRightHalfPlaneArgument
open GaussianRightHalfPlaneArgumentExponential (smallExpData large_exponential)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "C" => GaussianNameConjugation.nameF

def unsignedExpData (A B : PTm n) : PTm n := ed radius (unsignedData A B)
def signedExpData (A B neg : PTm n) : PTm n := ed radius (data A B neg)
def wideProductF : PR 2 := multiplyF constantF (C (E smallF))
def wideProductData (A B : PTm n) : PTm n :=
  multiplyData constantF (C (E smallF)) imaginaryPoint (smallExpData B A)

theorem small_chart (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] crossEquivalent (E unsignedF) (E smallF) (unsignedExpData A B) (smallExpData A B) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (unsigned_input A B hA) (small_input A B hA hB) (unsigned_small A B hA hB)

theorem large_chart (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] lt A B) :
    Γ ⊢[PRAAx] crossEquivalent (E unsignedF) wideProductF (unsignedExpData A B) (wideProductData A B) := by
  have b := le_trans hA (le_of_lt hB)
  have e := GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (unsigned_input A B hA) (large_input A B b (le_of_lt hB)) (unsigned_large A B hA hB)
  exact cross_trans _ _ _ _ _ _ e (large_exponential A B (le_of_lt hB) b)

theorem nonnegative_imaginary (A B neg : PTm n) (hA : Γ ⊢[PRAAx] le one A) (h : Γ ⊢[PRAAx] neg ≐ zero) :
    Γ ⊢[PRAAx] crossEquivalent (E nameF) (E unsignedF) (signedExpData A B neg) (unsignedExpData A B) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (exponential_input A B neg (.andI hA (.orI₁ h))) (unsigned_input A B hA) (positive_sign A B neg hA h)

theorem nonpositive_imaginary (A B neg : PTm n) (hA : Γ ⊢[PRAAx] le one A) (h : Γ ⊢[PRAAx] neg ≐ one) :
    Γ ⊢[PRAAx] crossEquivalent (E nameF) (C (E unsignedF)) (signedExpData A B neg) (unsignedExpData A B) := by
  have u := unsigned_input A B hA
  have e := GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (exponential_input A B neg (.andI hA (.orI₂ h))) (GaussianNameConjugation.exponential_input _ _ _ u)
    (negative_sign A B neg hA h)
  exact cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ (GaussianNameConjugation.exponential_cross _ _ _ u))

theorem actual_right_half_plane_argument_exponential_charts_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (le one (var 0) ⟶
      ((le (var 1) (var 0) ⟶ crossEquivalent (E unsignedF) (E smallF) (unsignedExpData (var 0) (var 1))
        (smallExpData (var 0) (var 1))) ⋏
      (lt (var 0) (var 1) ⟶ crossEquivalent (E unsignedF) wideProductF (unsignedExpData (var 0) (var 1))
        (wideProductData (var 0) (var 1))))) :=
  closeUniv 2 (.impI (.andI (.impI (small_chart _ _ Prf.hyp1 Prf.hyp0)) (.impI (large_chart _ _ Prf.hyp1 Prf.hyp0))))

theorem actual_right_half_plane_argument_exponential_sign_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (le one (var 0) ⟶
      (((var 2 ≐ zero) ⟶ crossEquivalent (E nameF) (E unsignedF) (signedExpData (var 0) (var 1) (var 2))
        (unsignedExpData (var 0) (var 1))) ⋏
      ((var 2 ≐ one) ⟶ crossEquivalent (E nameF) (C (E unsignedF)) (signedExpData (var 0) (var 1) (var 2))
        (unsignedExpData (var 0) (var 1))))) :=
  closeUniv 3 (.impI (.andI (.impI (nonnegative_imaginary _ _ _ Prf.hyp1 Prf.hyp0))
    (.impI (nonpositive_imaginary _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentExponentialBranches
