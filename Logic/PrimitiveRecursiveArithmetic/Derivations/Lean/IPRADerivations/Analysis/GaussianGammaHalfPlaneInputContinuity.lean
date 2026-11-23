import IPRADerivations.Analysis.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.GaussianGammaInputContinuity
import IPRADerivations.Analysis.GaussianGammaRightHalfPlane
import IPRADerivations.Analysis.GaussianEulerLowerPowerCoefficients
import IPRADerivations.Analysis.GaussianNamedRateTransport

/-!
# The original Gamma observations at independently encoded inputs

Clear only the source denominators when comparing the original C7 names.
On the positive half-plane the verified inverse bound gives a numerical
continuity modulus for the original Gamma name itself.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfPlaneInputContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEncodingRescaling (fraction_rescale fraction_denominator_congr
  rescaled_source original_C7_rescale)
open GaussianGammaReciprocalInverse (lambdaNumerator lambdaDenominator inverseF inverseData
  lambda_positive inverse_regular inverse_disk inverse_product gammaF gammaData original_gamma_inverse)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (ofGaussian positive_product)
open ComplexLogarithmRemainder (scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem canonical_denominator {z R B D : PTm n}
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (e : Γ ⊢[PRAAx] B ≐ D) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R D := by
  have radius := congrMul (.eqRefl R) e
  exact .andI h.andE₁ (.andI (le_congr (.eqRefl one) e h.andE₂.andE₁)
    (le_congr (.eqRefl _) (congrMul radius radius) h.andE₂.andE₂))

/-- The two inputs can have different positive denominators. The rate
still concerns the original C7 data and the original accuracy schedule. -/
theorem original_C7_mixed_rate (s z w R B D : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hw : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source w R D)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D)
      one (unit (GaussianGammaInputContinuity.modulus s R))) :
    Γ ⊢[PRAAx] independentRate GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF
      (GaussianGammaC7Name.data z R B) (GaussianGammaC7Name.data w R D) one (unit s) := by
  let Z := scale D z
  let W := scale B w
  let H := D*B
  let F := GaussianGammaC7Name.nameF
  have hB := hz.andE₂.andE₁
  have hD := hw.andE₂.andE₁
  have hzH := rescaled_source z R B D hz hD
  have hwBD := rescaled_source w R D B hw hB
  have swap := mul_comm (Γ := Γ) B D
  have hwH := canonical_denominator hwBD swap
  have left : Γ ⊢[PRAAx] ofGaussian Z H ≐ ofGaussian z B := fraction_rescale z B D hB hD
  have right : Γ ⊢[PRAAx] ofGaussian W H ≐ ofGaussian w D :=
    (fraction_denominator_congr W H (B*D) swap.eqSymm).eqTrans (fraction_rescale w D B hD hB)
  have close := distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) hd
  have rescaled := GaussianGammaInputContinuity.original_C7_independent_rate s Z W R H hzH hwH close
  have dataEq := GaussianGammaRepeatedShift.C7_data_congr (.eqRefl W) (.eqRefl R) swap
  have rightReindex := GaussianGammaInputProperness.code_data_cross F _ _
    (GaussianGammaC7Name.name_regular W R (B*D) hwBD)
    (GaussianGammaC7Name.name_regular W R H hwH) dataEq
  have leftCross := cross_symm _ _ _ _ (original_C7_rescale z R B D hz hD)
  have rightCross := cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ (original_C7_rescale w R D B hw hB)) rightReindex
  exact GaussianNamedRateTransport.transport F F F F _ _ _ _ one (unit s)
    (unit_positive s) rescaled leftCross rightCross

/-- The original disk and an actual rational real margin of at least 1/A. -/
def source (z R B A : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏ le one R

theorem reciprocal_source (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B one A :=
  GaussianGammaRightHalfPlane.original_right_half_plane_source z R B A
    (.andI h.andE₂ h.andE₁.andE₂.andE₁) h.andE₁.andE₁ h.andE₁.andE₂.andE₂

/-- Pay for the square of the common inverse bound using a dyadic clock. -/
def inverseClock (s R A : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (lambdaDenominator R A*lambdaDenominator R A) s

def modulus (s R A : PTm n) : PTm n :=
  GaussianGammaInputContinuity.modulus (inverseClock s R A) R

@[simp] theorem subst_inverseClock {m : ℕ} (σ : Fin n → PTm m) (s R A : PTm n) :
    Syn.subst σ (inverseClock s R A) = inverseClock (Syn.subst σ s) (Syn.subst σ R) (Syn.subst σ A) := by
  simp [inverseClock]

@[simp] theorem subst_modulus {m : ℕ} (σ : Fin n → PTm m) (s R A : PTm n) :
    Syn.subst σ (modulus s R A) = modulus (Syn.subst σ s) (Syn.subst σ R) (Syn.subst σ A) := by
  simp [modulus]

private theorem observation_budget (p q s R A : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le
      (rateNumerator (lambdaDenominator R A*lambdaDenominator R A*one)
        (lambdaNumerator R one*lambdaNumerator R one*unit (inverseClock s R A)) p q *
        rateDenominator (unit s) p q)
      (rateNumerator one (unit s) p q *
        rateDenominator (lambdaNumerator R one*lambdaNumerator R one*unit (inverseClock s R A)) p q) := by
  let L := lambdaDenominator R A
  let K := lambdaNumerator R one
  let U := unit (inverseClock s R A)
  let N := K*K*U
  let C := unit p*unit q
  have hK := (lambda_positive R one A (le_refl (Γ := Γ) one) hA).andE₁
  have grow := mul_le_mul_right U (positive_product _ _ hK hK)
  have query : Γ ⊢[PRAAx] le (L*L*unit s) U := GaussianFastValueCut.query_budget (L*L) s
  have clear : Γ ⊢[PRAAx] le (L*L*unit s) N :=
    le_trans query (le_congr (one_mul U) (.eqRefl _) grow)
  have weighted := mul_le_mul_right (C*C) clear
  have total := add_le_add₂ weighted (le_refl (Γ := Γ) (N*(unit p+unit q)*unit s*C))
  exact le_congr (by dsimp only [C,N,L,K,U,rateNumerator,rateDenominator]; ipra_ring)
    (by dsimp only [C,N,K,U,rateNumerator,rateDenominator]; ipra_ring) total

/-- Both observations are from the verified original Gamma reciprocal
programs. The distance is bounded by 2^-p + 2^-q + 2^-s. -/
theorem original_gamma_observations (p q s z w R B D A : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B A) (hw : Γ ⊢[PRAAx] source w R D A)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D)
      one (unit (modulus s R A))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 gammaF p (gammaData z R B A))
      (ap2 gammaF q (gammaData w R D A)) (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let F := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data z R B
  let y := GaussianGammaC7Name.data w R D
  let u := inverseData z R B
  let v := inverseData w R D
  let L := lambdaDenominator R A
  let K := lambdaNumerator R one
  let M := unit (inverseClock s R A)
  have zr := reciprocal_source z R B A hz
  have wr := reciprocal_source w R D A hw
  have hK := (lambda_positive R one A (le_refl (Γ := Γ) one) hz.andE₁.andE₁).andE₁
  have hM : Γ ⊢[PRAAx] le one M := unit_positive _
  have c7 := original_C7_mixed_rate (inverseClock s R A) z w R B D zr.andE₁ wr.andE₁ hd
  have hin : Γ ⊢[PRAAx] GaussianNamedInverseRate.input F F inverseF inverseF x y u v L K one M :=
    .andI hK (.andI hM
      (.andI (.andI (GaussianGammaC7Name.name_regular z R B zr.andE₁)
        (GaussianGammaC7Name.name_regular w R D wr.andE₁))
        (.andI (.andI (inverse_regular z R B zr.andE₁) (inverse_regular w R D wr.andE₁))
          (.andI (.andI (inverse_disk z R B one A zr) (inverse_disk w R D one A wr))
            (.andI (.andI (inverse_product z R B one A zr) (inverse_product w R D one A wr)) c7)))))
  have inv := GaussianNamedInverseRate.inverse_rate F F inverseF inverseF x y u v L K one M hin
  have pos : Γ ⊢[PRAAx] le one (K*K*M) := positive_product _ _ (positive_product _ _ hK hK) hM
  have old := GaussianNamedRateTransport.observation_error inverseF inverseF gammaF gammaF u v
    (gammaData z R B A) (gammaData w R D A) (L*L*one) (K*K*M) p q pos inv
    (original_gamma_inverse z R B one A zr).andE₂ (original_gamma_inverse w R D one A wr).andE₂
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ pos)
    (denominator_positive _ _ _ (unit_positive s)) (observation_budget p q s R A hz.andE₁.andE₁) old

theorem original_gamma_mixed_half_plane_input_continuity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((source (var 3) (var 5) (var 6) (var 8) ⋏
        (source (var 4) (var 5) (var 7) (var 8) ⋏
          distanceBounded (ofGaussian (var 3) (var 6)) (ofGaussian (var 4) (var 7)) one
            (unit (modulus (var 2) (var 5) (var 8))))) ⟶
        distanceBounded (ap2 gammaF (var 0) (gammaData (var 3) (var 5) (var 6) (var 8)))
          (ap2 gammaF (var 1) (gammaData (var 4) (var 5) (var 7) (var 8)))
          (rateNumerator one (unit (var 2)) (var 0) (var 1))
          (rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 9 (.impI (original_gamma_observations _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaHalfPlaneInputContinuity
