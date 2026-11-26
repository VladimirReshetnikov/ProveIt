import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpDegreeSchedule
import IPRADerivations.Analysis.Beta.Tails.GaussianBetaContiguousUpperTailBudget
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalL1Algebra

/-!
# Numerical evaluation of the documented sharp Euler degree

The degree itself is unchanged. A computed original decay observation
pays the raw L1 radius and its one ordinary observation error. The
existing general L1<=2 norm inequality suffices; no real-axis sampler
identification or altered polynomial degree is required.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpScheduleBudget

open_ipra
open GaussianEulerSharpDegreeSchedule (degree height size coefficient tailCoefficient degree_is_four_height height_positive)
open GaussianWeightedHalfDecayEndpoint (coefficient_positive)
open GaussianBetaContiguousUpperTail (quarterSample sampleNumerator sampleDenominator)
open GaussianBetaContiguousUpperTailBudget (fixedNumerator fixedDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul canonical positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive qL1 qL1_represents)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def decayClock (p R : PTm n) : PTm n := GaussianFastValueCut.exponent (num 5*tailCoefficient R) (p+num 4)
def mainNumerator (p R : PTm n) : PTm n :=
  coefficient R*fixedDenominator (decayClock p R) (degree p R)+fixedNumerator (decayClock p R) R (degree p R)*degree p R
def mainDenominator (p R : PTm n) : PTm n := degree p R*fixedDenominator (decayClock p R) (degree p R)
ipra_subst decayClock

theorem weighted_raw_l1_bound (q D X Y : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (hD : Γ ⊢[PRAAx] le one D) (hY : Γ ⊢[PRAAx] le one Y)
    (h : Γ ⊢[PRAAx] bounded (qmul (radiusPoint D one) q) X Y) : Γ ⊢[PRAAx]
    le (D*GaussianL1.norm1 (rawGaussian q)*Y) ((two*X)*rawDen q) := by
  let r := radiusPoint one D
  let w := radiusPoint D one
  have inv := bounded_product r (qmul w q) one D X Y hD hY (radius_bounded one D hD) h
  have same : Γ ⊢[PRAAx] qmul r (qmul w q) ≐ q :=
    (GaussianReciprocalHorner.qmul_associative r w q).eqSymm.eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (GaussianEulerWeightedHalfDecay.radius_reciprocal D one hD (le_refl one)) (.eqRefl _)).eqTrans
        (GaussianPolynomialDeterminantTerms.one_mul_canonical q hq))
  have point : Γ ⊢[PRAAx] bounded q X (Y*D) := bound_congr same (one_mul X) (mul_comm _ _) inv
  have l1 := GaussianRationalL1Algebra.qL1_of_bounded q X (Y*D) (positive_product _ _ hY hD) point
  have clear := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (qL1_represents q (rawGaussian q) (rawDen q) (raw_den_positive q) (raw_represents q))
    (RationalIntegerNormalization.normalize_preserves_value _ _ (positive_product _ _ hY hD)) l1
  exact le_congr (by ipra_ring) (.eqRefl _) clear

theorem degree_covers_radius (p R : PTm n) : Γ ⊢[PRAAx] le (two*R) (degree p R) := by
  have natural := LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract.le_pow_self (Γ := Γ) R
  have next := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_succ_self R)
  have fact : Γ ⊢[PRAAx] le (unit (succ R)) (tailCoefficient R) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (unit (succ R)) (GaussianRationalPolynomialExponential.factorial_positive R))
  have hs : Γ ⊢[PRAAx] le (tailCoefficient R) (size p R) :=
    le_of_eq_add (d := coefficient R+p+num 10) (by unfold size; ipra_ring)
  have heightGrow : Γ ⊢[PRAAx] le (size p R) (height p R) :=
    le_congr (one_mul _) (by unfold height; ipra_ring) (mul_le_mul_right (size p R) (unit_positive (p+num 4)))
  have base := le_trans natural (le_trans next (le_trans fact (le_trans hs heightGrow)))
  have twice := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right two base)
  exact le_trans twice (le_of_eq_add (d := two*height p R) (by
    exact (degree_is_four_height p R).eqTrans (by ipra_ring)))

theorem decay_clock_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (num 5*tailCoefficient R*unit (p+num 4)) (unit (decayClock p R)) := GaussianFastValueCut.query_budget _ _

theorem fixed_tail_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (fixedNumerator (decayClock p R) R (degree p R)*unit (p+num 4))
      (num 3*fixedDenominator (decayClock p R) (degree p R)) := by
  let q := decayClock p R
  let N := degree p R
  let D := tailCoefficient R
  let E := sampleDenominator q N
  have point : Γ ⊢[PRAAx] canonical (quarterSample q N) := GaussianRadiusExponentialName.sample_canonical _ _ _ _
  have raw := weighted_raw_l1_bound (quarterSample q N) D (unit q+two*D*unit (p+num 4)) (unit (p+num 4)*unit q)
    point (coefficient_positive R) (positive_product _ _ (unit_positive _) (unit_positive q))
    (GaussianEulerSharpDegreeSchedule.original_weighted_decay_bound p R q)
  have combined := add_le_add_right (D*E*unit (p+num 4)) raw
  have first : Γ ⊢[PRAAx] le (fixedNumerator q R N*unit (p+num 4)) ((two*unit q+num 5*D*unit (p+num 4))*E) :=
    le_congr (by dsimp only [fixedNumerator,sampleNumerator,sampleDenominator,D,E,GaussianWeightedHalfDecayEndpoint.coefficient,tailCoefficient]; ipra_ring)
      (by dsimp only [E,sampleDenominator]; ipra_ring) combined
  have budget := mul_le_mul_right E (add_le_add_right (two*unit q) (decay_clock_budget (Γ := Γ) p R))
  exact le_trans first (le_congr (by dsimp only [D,q]; ipra_ring) (by unfold fixedDenominator; ipra_ring) budget)

theorem main_budget (p R : PTm n) : Γ ⊢[PRAAx]
    le (mainNumerator p R*unit (p+num 4)) (num 5*mainDenominator p R) := by
  have next : Γ ⊢[PRAAx] unit (p+num 4) ≐ two*unit (p+num 3) :=
    ((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] p+num 4 ≐ succ (p+num 3)) (.eqRefl two)).eqTrans
      (pw_succ two (p+num 3))).eqTrans (mul_comm _ _)
  have c := mul_le_mul_right (two*fixedDenominator (decayClock p R) (degree p R))
    (GaussianEulerSharpDegreeSchedule.coefficient_budget (Γ := Γ) p R)
  have t := mul_le_mul_right (degree p R) (fixed_tail_budget (Γ := Γ) p R)
  have first : Γ ⊢[PRAAx] le ((coefficient R*fixedDenominator (decayClock p R) (degree p R))*unit (p+num 4))
      (two*mainDenominator p R) := le_congr (by
        apply deriveNat
        have eq := natEq next
        ipra_simps
        rw [eq]
        ring) (by unfold mainDenominator; ipra_ring) c
  exact le_congr (by unfold mainNumerator; ipra_ring) (by unfold mainDenominator; ipra_ring) (add_le_add₂ first t)

theorem literal_sharp_degree_covers_original_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (two*var 1) (degree (var 0) (var 1))) := closeUniv 2 (degree_covers_radius _ _)
theorem literal_sharp_degree_evaluated_coefficient_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (mainNumerator (var 0) (var 1)*unit ((var 0)+num 4)) (num 5*mainDenominator (var 0) (var 1))) :=
  closeUniv 2 (main_budget _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerSharpScheduleBudget
