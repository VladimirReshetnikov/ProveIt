import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaHalfPlaneInputContinuity
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# A uniform modulus for the original Gamma on certified pole-free inputs

The mixed-denominator reciprocal-Gamma modulus already applies on the
full disk. A common explicit pole guard supplies the same inverse bound
for both inputs. This yields a Gamma modulus without a half-plane premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaHalfPlaneInputContinuity (modulus inverseClock original_C7_mixed_rate)
open GaussianGammaReciprocalInverse (source gammaF gammaData inverseF inverseData inverse_disk inverse_regular
  inverse_product lambdaNumerator lambdaDenominator lambda_positive original_gamma_inverse)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_rate (s z w R B D E : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B one E) (hw : Γ ⊢[PRAAx] source w R D one E)
    (hIn : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (modulus s R E))) :
    Γ ⊢[PRAAx] independentRate gammaF gammaF (gammaData z R B E) (gammaData w R D E) one (unit s) := by
  let F := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data z R B
  let y := GaussianGammaC7Name.data w R D
  let u := inverseData z R B
  let v := inverseData w R D
  let L := lambdaDenominator R E
  let K := lambdaNumerator R one
  let M := unit (inverseClock s R E)
  have hK := (lambda_positive R one E (le_refl (Γ := Γ) one) hz.andE₂.andE₂.andE₁).andE₁
  have hM : Γ ⊢[PRAAx] le one M := unit_positive _
  have c7 := original_C7_mixed_rate (inverseClock s R E) z w R B D hz.andE₁ hw.andE₁ hIn
  have hin : Γ ⊢[PRAAx] GaussianNamedInverseRate.input F F inverseF inverseF x y u v L K one M :=
    .andI hK (.andI hM
      (.andI (.andI (GaussianGammaC7Name.name_regular z R B hz.andE₁)
        (GaussianGammaC7Name.name_regular w R D hw.andE₁))
        (.andI (.andI (inverse_regular z R B hz.andE₁) (inverse_regular w R D hw.andE₁))
          (.andI (.andI (inverse_disk z R B one E hz) (inverse_disk w R D one E hw))
            (.andI (.andI (inverse_product z R B one E hz) (inverse_product w R D one E hw)) c7)))))
  have inv := GaussianNamedInverseRate.inverse_rate F F inverseF inverseF x y u v L K one M hin
  have pos : Γ ⊢[PRAAx] le one (K*K*M) := positive_product _ _ (positive_product _ _ hK hK) hM
  have moved := GaussianNamedRateTransport.transport inverseF inverseF gammaF gammaF u v
    (gammaData z R B E) (gammaData w R D E) (L*L*one) (K*K*M) pos inv
    (original_gamma_inverse z R B one E hz).andE₂ (original_gamma_inverse w R D one E hw).andE₂
  have demand : Γ ⊢[PRAAx] le (L*L*unit s) M := GaussianFastValueCut.query_budget (L*L) s
  have comparison : Γ ⊢[PRAAx] le (L*L*one*unit s) (one*(K*K*M)) :=
    le_congr (by ipra_ring) (one_mul _).eqSymm
      (le_trans demand (le_congr (one_mul _) (.eqRefl _)
        (mul_le_mul_right M (positive_product _ _ hK hK))))
  exact GaussianNamedRateRadius.weaken gammaF gammaF _ _ _ _ _ _ pos (unit_positive s) comparison moved

theorem actual_original_pole_free_Gamma_mixed_modulus_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((source (var 1) (var 3) (var 4) one (var 6) ⋏ source (var 2) (var 3) (var 5) one (var 6)) ⟶
        distanceBounded (ofGaussian (var 1) (var 4)) (ofGaussian (var 2) (var 5)) one
          (unit (modulus (var 0) (var 3) (var 6))) ⟶
        independentRate gammaF gammaF (gammaData (var 1) (var 3) (var 4) (var 6))
          (gammaData (var 2) (var 3) (var 5) (var 6)) one (unit (var 0))) :=
  closeUniv 7 (.impI (.impI (original_rate _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeModulus
