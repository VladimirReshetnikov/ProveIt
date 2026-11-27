import IPRADerivations.Analysis.Euler.Integration.Parts.CompactNames.GaussianEulerIntegrationByPartsCompact
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaEulerShiftLimit

/-!
# Actual regular compact names in Euler integration by parts

Both original integrands use the same physical positive interval and a
common derived radius R+1. The left program is the normalized difference
of z times the original compact integral and its shifted compact integral.
The right program is the normalized difference of the original shifted
Euler names at the two true endpoints. Zero-width intervals are admitted.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCompactNames

open_ipra
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianRationalHorner (ofGaussian)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev compactF : PR 2 := GaussianEulerCompactAdditivity.nameF
abbrev productF : PR 2 := multiplyF constantF compactF
abbrev leftF : PR 2 := GaussianNamedDifference.nameF productF compactF
abbrev boundaryF : PR 2 := GaussianNamedDifference.nameF GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF

def compactData (z R B a C E T : PTm n) : PTm n := GaussianEulerCompactAdditivity.data z (R+one) B a C E T
def productData (z R B a C E T : PTm n) : PTm n := multiplyData constantF compactF (ofGaussian z B) (compactData z R B a C E T)
def leftData (z R B a C E T : PTm n) : PTm n :=
  GaussianNamedDifference.data (productData z R B a C E T) (compactData (shifted z B) R B a C E T)
def boundaryData (z B a C E : PTm n) : PTm n := GaussianNamedDifference.data
  (GaussianEulerIntegrandName.data (shifted z B) B (a+C) E) (GaussianEulerIntegrandName.data (shifted z B) B a E)
def productModulus (z R B a C E T : PTm n) : PTm n :=
  multiplyModulus constantF compactF (ofGaussian z B) (compactData z R B a C E T)

ipra_subst compactData
ipra_subst productData
ipra_subst leftData
ipra_subst boundaryData
ipra_subst productModulus

theorem common_sources (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    intervalSource z (R+one) B a C E T ⋏ intervalSource (shifted z B) (R+one) B a C E T := by
  have hz := ComplexLogarithmRemainder.bounded_mono h.andE₁.andE₂.andE₂
    (mul_le_mul_right B (le_add_right R one))
  have hs := GaussianGammaEulerShiftLimit.shifted_bound z R B h.andE₁.andE₂.andE₂
  exact .andI (.andI (.andI h.andE₁.andE₁ (.andI h.andE₁.andE₂.andE₁ hz)) h.andE₂)
    (.andI (.andI h.andE₁.andE₁ (.andI h.andE₁.andE₂.andE₁ hs)) h.andE₂)

theorem compact_regular (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    pointCN compactF (compactData z R B a C E T) ⋏ pointCN compactF (compactData (shifted z B) R B a C E T) :=
  .andI (GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ (common_sources z R B a C E T h).andE₁)
    (GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ (common_sources z R B a C E T h).andE₂)

theorem product_regular (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    pointCN productF (productData z R B a C E T) :=
  multiply_fast constantF compactF _ _ (constant_regular _) (compact_regular z R B a C E T h).andE₁

theorem left_regular (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    pointCN leftF (leftData z R B a C E T) :=
  GaussianNamedDifference.name_regular productF compactF _ _ (product_regular z R B a C E T h) (compact_regular z R B a C E T h).andE₂

theorem endpoint_regular (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    pointCN GaussianEulerIntegrandName.nameF (GaussianEulerIntegrandName.data (shifted z B) B (a+C) E) ⋏
      pointCN GaussianEulerIntegrandName.nameF (GaussianEulerIntegrandName.data (shifted z B) B a E) :=
  .andI (GaussianEulerIntegrandName.name_regular _ _ _ _ (.andI h.andE₁.andE₁ (.andI (le_trans h.andE₂.andE₁ (le_add_right a C)) h.andE₁.andE₂.andE₁)))
    (GaussianEulerIntegrandName.name_regular _ _ _ _ (.andI h.andE₁.andE₁ (.andI h.andE₂.andE₁ h.andE₁.andE₂.andE₁)))

theorem boundary_regular (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    pointCN boundaryF (boundaryData z B a C E) :=
  GaussianNamedDifference.name_regular _ _ _ _ (endpoint_regular z R B a C E T h).andE₁ (endpoint_regular z R B a C E T h).andE₂

theorem actual_original_compact_IBP_regular_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (intervalSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      pointCN leftF (leftData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ⋏
        pointCN boundaryF (boundaryData (var 0) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 7 (.impI (.andI (left_regular _ _ _ _ _ _ _ Prf.hyp0) (boundary_regular _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCompactNames
