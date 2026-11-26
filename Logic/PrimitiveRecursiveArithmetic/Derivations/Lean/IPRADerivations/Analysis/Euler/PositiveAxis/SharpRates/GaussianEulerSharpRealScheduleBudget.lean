import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpScheduleBudget
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayRealSamples

/-!
# The literal sharp degree with the exact real decay radius

The original decay observation is exactly real, so its actual raw L1
radius equals its Euclidean radius. Keep the preceding degree and decay
clock unchanged. The fixed tail coefficient is at most 8/5 times
2^-(p+4), hence at most 2*2^-(p+4), including its one original observation
error. The coefficient term itself is at most one quarter of 2^-(p+4).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpRealScheduleBudget

open_ipra
open GaussianEulerSharpDegreeSchedule (degree size coefficient tailCoefficient)
open GaussianEulerSharpScheduleBudget (decayClock mainNumerator mainDenominator decay_clock_budget)
open GaussianWeightedHalfDecayEndpoint (coefficient_positive)
open GaussianBetaContiguousUpperTail (quarterSample sampleNumerator sampleDenominator)
open GaussianBetaContiguousUpperTailBudget (fixedNumerator fixedDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem weighted_real_raw_l1_bound (q D X Y : PTm n)
    (hq : Γ ⊢[PRAAx] GaussianRationalConjugation.point q ≐ q)
    (hD : Γ ⊢[PRAAx] le one D) (hY : Γ ⊢[PRAAx] le one Y)
    (h : Γ ⊢[PRAAx] bounded (qmul (radiusPoint D one) q) X Y) : Γ ⊢[PRAAx]
    le (D*GaussianL1.norm1 (rawGaussian q)*Y) (X*rawDen q) := by
  have inv := bounded_product (radiusPoint one D) (qmul (radiusPoint D one) q) one D X Y
    hD hY (radius_bounded one D hD) h
  have canonical := GaussianRationalHorner.canonical_congr hq.eqSymm (GaussianRationalConjugation.point_canonical q)
  have same : Γ ⊢[PRAAx] qmul (radiusPoint one D) (qmul (radiusPoint D one) q) ≐ q :=
    (GaussianReciprocalHorner.qmul_associative _ _ q).eqSymm.eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (GaussianEulerWeightedHalfDecay.radius_reciprocal D one hD (le_refl one)) (.eqRefl _)).eqTrans
        (GaussianPolynomialDeterminantTerms.one_mul_canonical q canonical))
  have point : Γ ⊢[PRAAx] bounded q X (Y*D) := bound_congr same (one_mul X) (mul_comm _ _) inv
  exact le_congr (by ipra_ring) (.eqRefl _) (Prf.impE (GaussianEulerDecayRealSamples.fixed_bound_iff_raw_radius q X (Y*D)
    hq (positive_product _ _ hY hD)).andE₁ point)

theorem fixed_tail_exact_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (num 5*fixedNumerator (decayClock p R) R (degree p R)*unit (p+num 4))
      (num 8*fixedDenominator (decayClock p R) (degree p R)) := by
  let q := decayClock p R
  let N := degree p R
  let D := tailCoefficient R
  let E := sampleDenominator q N
  have realSample := GaussianEulerDecayRealSamples.original_observation_fixed (Γ := Γ) q N (num 4)
    (GaussianEulerSharpDegreeSchedule.four_positive (Γ := Γ))
  have raw := weighted_real_raw_l1_bound (quarterSample q N) D (unit q+two*D*unit (p+num 4)) (unit (p+num 4)*unit q)
    realSample (coefficient_positive R) (positive_product _ _ (unit_positive _) (unit_positive q))
    (GaussianEulerSharpDegreeSchedule.original_weighted_decay_bound p R q)
  have combined := mul_le_mul_right (num 5) (add_le_add_right (D*E*unit (p+num 4)) raw)
  have first : Γ ⊢[PRAAx]
      le (num 5*fixedNumerator q R N*unit (p+num 4)) ((num 5*unit q+num 15*D*unit (p+num 4))*E) :=
    le_congr (by dsimp only [fixedNumerator,sampleNumerator,sampleDenominator,D,E,GaussianWeightedHalfDecayEndpoint.coefficient,tailCoefficient]; ipra_ring)
      (by dsimp only [E,sampleDenominator]; ipra_ring) combined
  have budget := mul_le_mul_right (num 3*E) (decay_clock_budget (Γ := Γ) p R)
  have final := add_le_add_right (num 5*unit q*E) budget
  exact le_trans first (le_congr (by dsimp only [D,q]; ipra_ring) (by unfold fixedDenominator; ipra_ring) final)

theorem fixed_tail_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (fixedNumerator (decayClock p R) R (degree p R)*unit (p+num 4))
      (two*fixedDenominator (decayClock p R) (degree p R)) := by
  apply mul_le_cancel (d' := num 4)
  exact le_trans (le_congr (by ipra_ring) (.eqRefl _) (fixed_tail_exact_budget p R))
    (le_of_eq_add (d := two*fixedDenominator (decayClock p R) (degree p R)) (by ipra_ring))

theorem coefficient_quarter_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (num 4*coefficient R*unit (p+num 4)) (degree p R) := by
  have h : Γ ⊢[PRAAx] le (coefficient R) (size p R) :=
    le_of_eq_add (d := tailCoefficient R+p+num 10) (by unfold size; ipra_ring)
  exact le_congr (by ipra_ring) (by unfold degree; ipra_ring) (mul_le_mul_right (num 4*unit (p+num 4)) h)

theorem main_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (mainNumerator p R*unit (p+num 4)) (num 3*mainDenominator p R) := by
  have c : Γ ⊢[PRAAx] le (coefficient R*unit (p+num 4)) (degree p R) :=
    le_trans (le_of_eq_add (d := num 3*coefficient R*unit (p+num 4)) (by ipra_ring)) (coefficient_quarter_budget p R)
  have first := mul_le_mul_right (fixedDenominator (decayClock p R) (degree p R)) c
  have second := mul_le_mul_right (degree p R) (fixed_tail_budget (Γ := Γ) p R)
  exact le_congr (by unfold mainNumerator; ipra_ring) (by unfold mainDenominator; ipra_ring) (add_le_add₂ first second)

theorem literal_sharp_degree_real_tail_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (num 5*fixedNumerator (decayClock (var 0) (var 1)) (var 1) (degree (var 0) (var 1))*unit ((var 0)+num 4))
      (num 8*fixedDenominator (decayClock (var 0) (var 1)) (degree (var 0) (var 1)))) :=
  closeUniv 2 (fixed_tail_exact_budget _ _)
theorem literal_sharp_degree_real_main_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (mainNumerator (var 0) (var 1)*unit ((var 0)+num 4)) (num 3*mainDenominator (var 0) (var 1))) :=
  closeUniv 2 (main_budget _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerSharpRealScheduleBudget
