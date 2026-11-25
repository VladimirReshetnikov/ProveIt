import IPRADerivations.Analysis.GaussianEulerPositiveTimePowerProduct
import IPRADerivations.Analysis.GaussianPositiveRationalLogarithmProperness

/-!
# Logarithm increment at a positive rational argument

The maintained rational and harmonic logarithm names satisfy the exact
identity log((a+b)/b) = log(a/b) + log((a+b)/a).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingRationalLogShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (addF addData add_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal cross_trans)
open GaussianPositiveRationalLogarithm (logF data source name_regular)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data

theorem increment (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent H (addF H logF) (hd (a+b) b) (addData (hd a b) (data (a+b) a)) := by
  have pos := le_trans hs.andE₁ (le_add_right a b)
  have hShift : Γ ⊢[PRAAx] source (a+b) b := .andI pos hs.andE₂
  have hRatio : Γ ⊢[PRAAx] source (a+b) a := .andI pos hs.andE₁
  have hProduct : Γ ⊢[PRAAx] source (a*(a+b)) (b*a) :=
    .andI (positive_product _ _ hs.andE₁ pos) (positive_product _ _ hs.andE₂ hs.andE₁)
  have product := GaussianEulerPositiveTimePowerProduct.logarithm_product a b (a+b) a (.andI hs hRatio)
  have same := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper (a+b) b (a*(a+b)) (b*a)
    hShift hProduct (by ipra_ring)
  have shift := GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original (a+b) b hShift)
  have original := GaussianHarmonicLogarithmName.cross_original a b hs
  have hx := name_regular a b hs
  have hy := name_regular (a+b) a hRatio
  have lift := add_equivalent logF H logF logF (data a b) (hd a b) (data (a+b) a) (data (a+b) a)
    hx (GaussianHarmonicLogarithmName.name_regular a b hs) hy hy
    (cross_to_diagonal _ _ _ _ original) (GaussianNameEquivalence.diagonal_refl logF (data (a+b) a))
  exact cross_trans _ _ _ _ _ _ shift (cross_trans _ _ _ _ _ _ same (cross_trans _ _ _ _ _ _ product lift))

set_option maxHeartbeats 1600000 in
theorem actual_positive_rational_Stirling_log_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent H (addF H logF) (hd (var 0+var 1) (var 1))
      (addData (hd (var 0) (var 1)) (data (var 0+var 1) (var 0)))) :=
  closeUniv 2 (.impI (increment _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingRationalLogShift
