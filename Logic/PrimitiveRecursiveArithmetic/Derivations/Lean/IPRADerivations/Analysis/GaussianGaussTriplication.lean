import IPRADerivations.Analysis.GaussianGaussExplicitShiftedProducts
import IPRADerivations.Analysis.GaussianGaussMultiplicationHalfPowers
import IPRADerivations.Analysis.GaussianGaussTriplicationPi

/-!
# The original Gamma triplication identity

At order three the shifted product has three literal Gamma rows.
The first half power of twice pi agrees with the original doubled
pi name, yielding the explicit triplication formula.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussTriplication

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGaussExplicitShiftedProducts (threeRowsF threeRowsData three_factors)
open GaussianGaussMultiplicationCofinalRows (scaled_regular scaledData)
open GaussianGaussMultiplicationHalfPower (ratioPowerF ratio_power_regular regroupedCoefficient regroupedData)
open GaussianGaussMultiplicationHalfPowers (normalizedF normalizedData coefficientF coefficientData normalized_multiplication)
open GaussianGaussTriplicationPi (doubledPiF doubledPiData doubled_pi_regular pi_half_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "PiHalf" => GaussianGaussPiPowerSquareRoot.nameF

abbrev triplicationCoefficientF : PR 2 := multiplyF doubledPiF ratioPowerF
abbrev triplicationF : PR 2 := multiplyF triplicationCoefficientF gammaF
def triplicationCoefficientData (z B x : PTm n) : PTm n :=
  multiplyData doubledPiF ratioPowerF (doubledPiData x) (regroupedData z B (succ two))
def triplicationData (z R B d x : PTm n) : PTm n :=
  multiplyData triplicationCoefficientF gammaF (triplicationCoefficientData z B x) (scaledData z R B (succ two) d)

theorem triplication_right (z R B a d x : PTm n) (hs : Γ ⊢[PRAAx] source z R B (succ two) a d) :
    Γ ⊢[PRAAx] crossEquivalent normalizedF triplicationF (normalizedData z R B two d x)
      (triplicationData z R B d x) := by
  let Y := GaussianGaussPiPowerSquareRoot.nameData two x
  let D := doubledPiData x
  let Q := regroupedData z B (succ two)
  let G := scaledData z R B (succ two) d
  have hY := GaussianGaussPiPowerSquareRoot.name_regular (Γ := Γ) two x
  have hD := doubled_pi_regular (Γ := Γ) x
  have hQ := ratio_power_regular (regroupedCoefficient z B (succ two)) (succ two) hs.andE₁.andE₁
  have hG := scaled_regular z R B (succ two) a d hs
  have coefficients := multiply_cross PiHalf doubledPiF ratioPowerF ratioPowerF Y D Q Q hY hD hQ hQ
    (pi_half_cross x) (cross_refl _ _ hQ)
  exact multiply_cross coefficientF triplicationCoefficientF gammaF gammaF (coefficientData z B two x)
    (triplicationCoefficientData z B x) G G
    (multiply_fast _ _ _ _ hY hQ) (multiply_fast _ _ _ _ hD hQ) hG hG coefficients (cross_refl _ _ hG)

theorem triplication (z R B a d x : PTm n) (hs : Γ ⊢[PRAAx] source z R B (succ two) a d) :
    Γ ⊢[PRAAx] crossEquivalent threeRowsF triplicationF (threeRowsData z R B (succ two) d) (triplicationData z R B d x) :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (three_factors z R B a d hs))
    (cross_trans _ _ _ _ _ _ (normalized_multiplication z R B two a d x hs) (triplication_right z R B a d x hs))

theorem actual_Gauss_triplication_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (succ two) (var 3) (var 4) ⟶ crossEquivalent threeRowsF triplicationF
      (threeRowsData (var 0) (var 1) (var 2) (succ two) (var 4))
      (triplicationData (var 0) (var 1) (var 2) (var 4) (var 5))) :=
  closeUniv 6 (.impI (triplication _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussTriplication
