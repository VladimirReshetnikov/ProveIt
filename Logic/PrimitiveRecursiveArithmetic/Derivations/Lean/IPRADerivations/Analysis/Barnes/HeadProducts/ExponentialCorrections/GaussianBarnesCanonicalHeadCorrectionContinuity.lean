import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadCorrectionExponentialDerivative
import IPRADerivations.Analysis.Barnes.HeadProducts.Factors.GaussianBarnesCanonicalFactorLipschitz

/-!
# Disk continuity of the original finite Barnes exponential correction

The total correction is its literal harmonic quadratic and its slope
is affine. Both are compared at the supplied rational arguments. A
common radius bounds the exponential comparison, which is transported
back to the two original dynamically chosen radii.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadCorrectionContinuity

open_ipra
open GaussianBarnesCanonicalCorrectionShift (total)
open GaussianBarnesCanonicalHead (source)
open GaussianBarnesCanonicalHeadCorrectionDerivative (halfSquare slope total_formula)
open GaussianBarnesCanonicalHeadCorrectionExponentialDerivative (exponentRadius exponent_bound exponentialF)
open GaussianBarnesCanonicalHeadExponentialFactors (exponentData)
open GaussianGammaCanonicalExponent (constantF constant_regular harmonicPoint)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRadiusExponentialLipschitzRate (factor)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def totalGain (R N : PTm n) : PTm n := N*(two*R+one)
def gain (R N : PTm n) : PTm n := factor (exponentRadius R N)*totalGain R N

@[simp] theorem subst_totalGain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (totalGain R N) = totalGain (Syn.subst σ R) (Syn.subst σ N) := by simp [totalGain,one,two]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (gain R N) = gain (Syn.subst σ R) (Syn.subst σ N) := by simp [gain]

private theorem scale_left (c x y K A E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hc : Γ ⊢[PRAAx] bounded c K one) (hd : Γ ⊢[PRAAx] distanceBounded x y A E) :
    Γ ⊢[PRAAx] distanceBounded (qmul c x) (qmul c y) (K*A) E :=
  GaussianRationalRoundedPower.distance_mul_left_one hE hc hd

private theorem scale_right (x y c K A E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hc : Γ ⊢[PRAAx] bounded c K one) (hd : Γ ⊢[PRAAx] distanceBounded x y A E) :
    Γ ⊢[PRAAx] distanceBounded (qmul x c) (qmul y c) (K*A) E :=
  distance_congr (qmul_commutative c x) (qmul_commutative c y) (.eqRefl _) (.eqRefl _)
    (scale_left c x y K A E hE hc hd)

theorem slope_distance (z w B D N A E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A E) :
    Γ ⊢[PRAAx] distanceBounded (slope z B N) (slope w D N) (N*A) E := by
  let x := qmul (ofGaussian z B) (harmonicPoint N)
  let y := qmul (ofGaussian w D) (harmonicPoint N)
  let k := naturalPoint N
  have dx := scale_right (ofGaussian z B) (ofGaussian w D) (harmonicPoint N) N A E hE
    (GaussianGammaCanonicalExponentBound.harmonic_point_bound N) hd
  have dz := GaussianRationalPowerDifference.distance_refl_zero k E hE
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_zero _) (.eqRefl _)
    (GaussianNamedDifference.difference_distance x y k k _ _ E hE dx dz)

private theorem half_denominator_grows (B : PTm n) : Γ ⊢[PRAAx] le B (two*B) :=
  le_congr (one_mul B) (.eqRefl _) (mul_le_mul_right B (le_succ_self one))

private theorem half_bound (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ofGaussian z (two*B)) R one :=
  GaussianGammaEulerHead.fraction_disk z R (two*B) (le_trans hz.andE₁ (half_denominator_grows B))
    (ComplexLogarithmRemainder.bounded_mono hz.andE₂ (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono
      (le_refl R) (half_denominator_grows B)))

private theorem half_distance (z w B D A E : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A E) :
    Γ ⊢[PRAAx] distanceBounded (ofGaussian z (two*B)) (ofGaussian w (two*D)) A E := by
  have htwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have h := GaussianBarnesCanonicalFactorLipschitz.scaled_fraction_distance z w B D two A E hB hD htwo hE hd
  have ez := GaussianGammaEncodingRescaling.fraction_denominator_congr (Γ := Γ) z (B*two) (two*B) (mul_comm B two)
  have ew := GaussianGammaEncodingRescaling.fraction_denominator_congr (Γ := Γ) w (D*two) (two*D) (mul_comm D two)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE htwo) hE
    (by ipra_le 𝔞(A*E)*sl htwo) (distance_congr ez ew (.eqRefl _) (.eqRefl _) h)

theorem total_distance (z w R B D N A E : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (hE : Γ ⊢[PRAAx] le one E)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A E) :
    Γ ⊢[PRAAx] distanceBounded (total z B N) (total w D N) (totalGain R N*A) E := by
  let x := ofGaussian z B
  let y := ofGaussian w D
  let s := ofGaussian z (two*B)
  let t := ofGaussian w (two*D)
  let H := harmonicPoint N
  let k := naturalPoint N
  have half := half_distance z w B D A E hz.andE₁ hw.andE₁ hE hd
  have sq : Γ ⊢[PRAAx] distanceBounded (halfSquare z B) (halfSquare w D) (A*R+R*A) E :=
    GaussianNameArithmetic.product_distance x y s t A A E R R hE hd half (half_bound z R B hz)
      (GaussianGammaEulerHead.fraction_disk w R D hw.andE₁ hw.andE₂)
  have first := scale_right (halfSquare z B) (halfSquare w D) H N (A*R+R*A) E hE
    (GaussianGammaCanonicalExponentBound.harmonic_point_bound N) sq
  have last := scale_left k x y N A E hE (GaussianNamedNaturalScale.natural_point_bound N) hd
  have dist := GaussianNamedDifference.difference_distance _ _ _ _ _ _ E hE first last
  exact distance_congr (total_formula z B N hz.andE₁).eqSymm (total_formula w D N hw.andE₁).eqSymm
    (by unfold totalGain; ipra_ring) (.eqRefl _) dist

theorem independent_rate (z w R B D N A E : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (hE : Γ ⊢[PRAAx] le one E)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A E) :
    Γ ⊢[PRAAx] independentRate exponentialF exponentialF (exponentData z B N) (exponentData w D N) (gain R N*A) E := by
  let C := constantF
  let F := exponentialF
  let S := exponentRadius R N
  let x := total z B N
  let y := total w D N
  let u := GaussianRadiusExponentialName.data S x
  let v := GaussianRadiusExponentialName.data S y
  have hX := GaussianSignedNameExponentialOrder.constant_input x S (exponent_bound z B N R hz.andE₁ hz.andE₂)
  have hY := GaussianSignedNameExponentialOrder.constant_input y S (exponent_bound w D N R hw.andE₁ hw.andE₂)
  have hA := GaussianNamedAddRate.constant_rate x y _ E hE (total_distance z w R B D N A E hz hw hE hd)
  have raw := GaussianRadiusExponentialLipschitzRate.independent_rate C C S x y (totalGain R N*A) E
    (.andI hE (.andI hX (.andI hY hA)))
  have fit : Γ ⊢[PRAAx] factor S*(totalGain R N*A) ≐ gain R N*A := by dsimp only [gain,S]; ipra_ring
  have base := GaussianNamedDifferenceRate.rate_parameters_congr F F u v _ _ _ _ fit (.eqRefl E) raw
  exact GaussianNamedRateTransport.transport F F F F u v (exponentData z B N) (exponentData w D N) _ E hE base
    (GaussianExponentialRadiusIndependence.same_input_cross C (GaussianNameBounds.U C x) S x
      (GaussianGammaFiniteApproximantName.exponential_input C x (constant_regular x)) hX)
    (GaussianExponentialRadiusIndependence.same_input_cross C (GaussianNameBounds.U C y) S y
      (GaussianGammaFiniteApproximantName.exponential_input C y (constant_regular y)) hY)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadCorrectionContinuity
