import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleFiniteFactors
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaRadiusOverlap

/-!
# The exact linear factor of the original reciprocal Gamma at a pole

On the encoded closed unit disk about -n, the original reciprocal
Gamma is the step times a regular-name product. The product is the
signed factorial, the actual normalized finite factors, and the
original reciprocal at the terminal argument 1+h/B. This identity
includes the pole itself.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleReciprocalFactor

open_ipra
open GaussianGammaLocalPoleGuards (center terminal center_source_disk terminal_source_disk)
open GaussianGammaPoleFiniteFactors (signedFactorial factorProduct centered_rising_factorization)
open GaussianGammaRepeatedShift (risingProduct original_C22)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianRationalHorner (qmul ofGaussian)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded)
open ComplexLogarithmRemainder (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quotientF : PR 2 := multiplyF constantF GaussianGammaC7Name.nameF
def quotientData (h B j : PTm n) : PTm n :=
  multiplyData constantF GaussianGammaC7Name.nameF
    (qmul (signedFactorial j) (factorProduct h B j)) (GaussianGammaC7Name.data (terminal h B j) two B)
def factoredF : PR 2 := multiplyF constantF quotientF
def factoredData (h B j : PTm n) : PTm n := multiplyData constantF quotientF (ofGaussian h B) (quotientData h B j)

theorem original_quotient_regular (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] bounded h B) : Γ ⊢[PRAAx] pointCN quotientF (quotientData h B j) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (GaussianGammaC7Name.name_regular _ _ _ (terminal_source_disk h B j hB hh))

theorem original_P_linear_factor (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] bounded h B) :
    Γ ⊢[PRAAx] crossEquivalent GaussianGammaC7Name.nameF factoredF
      (GaussianGammaC7Name.data (center h B j) (succ j) B) (factoredData h B j) := by
  let z := center h B j
  let w := terminal h B j
  let R := succ j
  let P := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data z R B
  let y := GaussianGammaC7Name.data w two B
  let Y := GaussianGammaC7Name.data w (R+succ j) B
  let k := risingProduct z B (succ j)
  let step := ofGaussian h B
  let c := qmul (signedFactorial j) (factorProduct h B j)
  have hz := center_source_disk h B j hB hh
  have hw := terminal_source_disk h B j hB hh
  have hW := GaussianGammaShiftTrajectory.point_source z R B (succ j) hz
  have hn : Γ ⊢[PRAAx] pointCN P y := GaussianGammaC7Name.name_regular _ _ _ hw
  have hN : Γ ⊢[PRAAx] pointCN P Y := GaussianGammaC7Name.name_regular _ _ _ hW
  have hk := constant_regular (Γ := Γ) k
  have o := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF P P k (qmul step c) Y y hk
    (constant_regular _) hN hn
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (centered_rising_factorization h B j hB))
    (GaussianGammaRadiusOverlap.original_P_overlap w (R+succ j) two B hW hw)
  have d := GaussianGammaEulerShift.merge_head P step c y hn
  exact cross_trans _ _ _ _ _ _ (original_C22 z R B j hz) (cross_trans _ _ _ _ _ _ o (cross_symm _ _ _ _ d))

theorem original_C23_linear_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ bounded (var 0) (var 1) ⟶
      crossEquivalent GaussianGammaC7Name.nameF factoredF
        (GaussianGammaC7Name.data (center (var 0) (var 1) (var 2)) (succ (var 2)) (var 1))
        (factoredData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (original_P_linear_factor _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_C23_factored_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ bounded (var 0) (var 1) ⟶ distanceBounded
      (GaussianGammaC7Name.sample (var 3) (center (var 0) (var 1) (var 2)) (succ (var 2)) (var 1))
      (ap2 factoredF (var 4) (factoredData (var 0) (var 1) (var 2)))
      (unit (var 3)+unit (var 4)) (unit (var 3)*unit (var 4))) :=
  closeUniv 5 (.impI (.impI (cross_at _ _ _ _ _ _
    (original_P_linear_factor _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleReciprocalFactor
