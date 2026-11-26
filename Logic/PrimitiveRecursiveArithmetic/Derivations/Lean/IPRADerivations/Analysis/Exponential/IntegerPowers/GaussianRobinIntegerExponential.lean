import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale
import IPRADerivations.Analysis.SpecialFunctions.LambertW.GaussianRobinLogRangeReduction
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialAddition
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialMajorant
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialInverse
import IPRADerivations.Analysis.Names.GaussianNameEquivalence
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallPerturbationTransport

/-!
# Integer multiples of the original Robin odd logarithm of two

A fixed numerical cap retains one original input clock at all stages.
The actual exponential addition theorem supplies one successor equation.
A numerical QF distance invariant, rather than induction over names,
identifies the actual scaled exponential with the computed power of two.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRobinIntegerExponential

open_ipra
open GaussianRationalHorner (canonical positive_product qmul)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRobinOddExponential (oddF constantF)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def baseData : PTm n := GaussianRobinOddLogarithmName.inputs one AnalyticNumberTheory.RobinLogInterval.c3
def scaledF : PR 2 := GaussianNamedNaturalScale.nameF oddF
def stageData (E i : PTm n) : PTm n := GaussianNamedNaturalScale.data E i baseData
def radius (E : PTm n) : PTm n := GaussianNamedNaturalScale.radius E (num 3)
def expF : PR 2 := GaussianRadiusExponentialName.nameF scaledF
def expData (E i : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius E) (stageData E i)
def point (p E i : PTm n) : PTm n := ap2 expF p (expData E i)
def baseValue : PTm n := GaussianRobinLogRangeReduction.quotient two one
def powerValue (i : PTm n) : PTm n := power baseValue i
def majorant (E : PTm n) : PTm n := pw (num 3) (radius E)
def stepCost (E : PTm n) : PTm n := two+num 4*majorant E+two*unit E
def multiplier (E : PTm n) : PTm n := majorant E+stepCost E+one
def error (E i : PTm n) : PTm n := pw (multiplier E) (succ i)

ipra_subst baseData [GaussianRobinOddLogarithmName.inputs]
ipra_subst stageData
ipra_subst radius
ipra_subst expData
ipra_subst point
ipra_subst baseValue [GaussianRobinLogRangeReduction.quotient, GaussianRobinLogarithmParity.native]
ipra_subst powerValue
ipra_subst majorant
ipra_subst stepCost
ipra_subst multiplier
ipra_subst error

theorem original_input : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input oddF (num 3) (baseData : PTm n) :=
  GaussianRobinOddExponential.odd_input _ _ (.andI (le_of_eq_add (d := two) (by ipra_ring))
    (le_of_eq_add (d := one) (by ipra_ring)))
theorem stage_input (E i : PTm n) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input scaledF (radius E) (stageData E i) :=
  GaussianNamedNaturalScale.exponential_input oddF E i (num 3) baseData original_input hi
theorem point_regular (E i : PTm n) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN expF (expData E i) :=
  GaussianRadiusExponentialName.name_regular scaledF _ _ (stage_input E i hi)
theorem point_canonical (p E i : PTm n) : Γ ⊢[PRAAx] canonical (point p E i) :=
  GaussianRadiusExponentialName.sample_canonical scaledF _ _ _
theorem point_bound (p E i : PTm n) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx] bounded (point p E i) (majorant E) one :=
  GaussianRationalReciprocal.bound_congr (GaussianRadiusExponentialName.sample_at scaledF (radius E) p (stageData E i)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _ (GaussianRadiusExponentialName.query_bound scaledF _ _ _ (stage_input E i hi)))

theorem point_zero (p E : PTm n) : Γ ⊢[PRAAx] point p E zero ≐ qone :=
  (GaussianRadiusExponentialName.sample_at scaledF (radius E) p (stageData E zero)).eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
      (GaussianNamedNaturalScale.sample_zero oddF _ E baseData)).eqTrans (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

theorem one_exponential (E : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    crossEquivalent expF constantF (expData E one) baseValue :=
  cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.independent_radii_proper scaledF oddF (radius E) (num 3) (stageData E one) baseData
      (stage_input E one hE) original_input (GaussianNamedNaturalScale.one_cross oddF E (num 3) baseData original_input))
    GaussianRobinLogRangeReduction.original_base_component

theorem power_value_code (i : PTm n) : Γ ⊢[PRAAx]
    powerValue i ≐ GaussianRationalNaturalScale.naturalPoint (unit i) :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalReciprocal.power_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) (le_refl one)
    (GaussianExponentialDiskMajorant.natural_power_represents two i)
    (GaussianRationalNaturalScale.natural_point_represents (unit i))
theorem power_bound (E i : PTm n) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx] bounded (powerValue i) (unit E) one := by
  have grow : Γ ⊢[PRAAx] le (unit i) (unit E) := GaussianFactorBudget.power_monotone_length two i E (le_succ_self one) hi
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) grow)
    (GaussianRationalReciprocal.bound_congr (power_value_code i).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianNamedNaturalScale.natural_point_bound (unit i)))

def productF : PR 2 := GaussianNameArithmetic.multiplyF expF expF
def productData (E i : PTm n) : PTm n := GaussianNameArithmetic.multiplyData expF expF (expData E i) (expData E one)
ipra_subst productData

theorem successor_exponential (E i : PTm n) (hi : Γ ⊢[PRAAx] le (succ i) E) : Γ ⊢[PRAAx]
    crossEquivalent productF expF (productData E i) (expData E (succ i)) := by
  have ii := le_trans (le_succ_self i) hi
  have oneE := le_trans (zero_lt_succ i) hi
  have a := GaussianExponentialAddition.exponential_add_cross scaledF scaledF (radius E) (stageData E i) (stageData E one)
    (GaussianNamedNaturalScale.radius_positive E (num 3)) (stage_input E i ii) (stage_input E one oneE)
  have b := GaussianExponentialRadiusIndependence.independent_radii_proper
    (GaussianNameArithmetic.addF scaledF scaledF) scaledF (radius E+radius E) (radius E)
    (GaussianNamedNaturalScale.addData E i baseData) (stageData E (succ i))
    (GaussianExponentialReference.add_input scaledF scaledF (radius E) (stageData E i) (stageData E one)
      (stage_input E i ii) (stage_input E one oneE)) (stage_input E (succ i) hi)
    (GaussianNamedNaturalScale.add_step_cross oddF E i (num 3) baseData original_input hi)
  exact cross_trans _ _ _ _ _ _ a b


theorem one_error (p E : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    distanceBounded (point p E one) baseValue two (unit p) := by
  have close := GaussianNameEquivalence.diagonal_at _ _ _ _ p
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (one_exponential E hE))
  exact distance_congr (.eqRefl _) (GaussianGammaCanonicalExponent.constant_at p baseValue) (.eqRefl _) (.eqRefl _) close

theorem later_point_error (p q E i : PTm n) (hi : Γ ⊢[PRAAx] le i E) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    distanceBounded (point q E i) (point p E i) two (unit p) :=
  GaussianNameEquivalence.point_at_later expF (expData E i) p q (point_regular E i hi) hpq

/-- The actual product name is compared to the two original observations
at p; its own larger normalization query is retained and bounded. -/
theorem product_same_precision (p E i : PTm n) (hi : Γ ⊢[PRAAx] le i E) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 productF p (productData E i)) (qmul (point p E i) (point p E one))
      (num 4*majorant E) (unit p) := by
  let s := GaussianNamedSmallPerturbationTransport.productClock expF expF (expData E i) (expData E one) p
  have later : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have raw := GaussianNameArithmetic.product_distance (point s E i) (point p E i) (point s E one) (point p E one)
    two two (unit p) (majorant E) (majorant E) (unit_positive p)
    (later_point_error p s E i hi later) (later_point_error p s E one hE later)
    (point_bound s E one hE) (point_bound p E i hi)
  exact distance_congr (GaussianNamedSmallPerturbationTransport.product_at expF expF _ _ p).eqSymm
    (.eqRefl _) (by ipra_ring) (.eqRefl _) raw

theorem successor_product_error (p E i : PTm n) (hi : Γ ⊢[PRAAx] le (succ i) E) : Γ ⊢[PRAAx]
    distanceBounded (point p E (succ i)) (qmul (point p E i) (point p E one))
      (two+num 4*majorant E) (unit p) := by
  have first := distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p))
    (cross_at _ _ _ _ p p (successor_exponential E i hi))
  have closer : Γ ⊢[PRAAx] distanceBounded (point p E (succ i)) (ap2 productF p (productData E i)) two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
      (le_of_eq_add (d := zero) (by ipra_ring)) first
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) closer
    (product_same_precision p E i (le_trans (le_succ_self i) hi) (le_trans (zero_lt_succ i) hi))

theorem multiplier_positive (E : PTm n) : Γ ⊢[PRAAx] le one (multiplier E) :=
  le_congr (.eqRefl _) (by unfold multiplier; ipra_ring) (le_add_right one (majorant E+stepCost E))
theorem error_positive (E i : PTm n) : Γ ⊢[PRAAx] le one (error E i) :=
  GaussianFactorBudget.power_positive _ _ (multiplier_positive E)
theorem error_growth (E i : PTm n) : Γ ⊢[PRAAx]
    le (majorant E*error E i+stepCost E) (error E (succ i)) := by
  have positive := error_positive (Γ := Γ) E i
  ipra_le 𝔞(stepCost E)*sl positive+𝔞(error E i) using
    unfold error
    rw [natEq (pw_succ (Γ := Γ) (multiplier E) (succ i))]
    unfold multiplier
    ipra_simps
    ring

theorem error_zero (p E : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (point p E zero) (powerValue zero) (error E zero) (unit p) := by
  have exactZero : Γ ⊢[PRAAx] distanceBounded (point p E zero) (powerValue zero) zero (unit p) := distance_congr (point_zero p E).eqSymm (GaussianRationalReciprocal.power_zero baseValue).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero qone (unit p) (unit_positive p))
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p)
    (le_of_eq_add (d := error E zero*unit p) (by ipra_ring)) exactZero

/-- Fixed-p numerical error propagation is the only induction step. The
base exponential identity is the actual original Robin 1/3 identity. -/
theorem error_step (p E i : PTm n) (hi : Γ ⊢[PRAAx] le (succ i) E)
    (ih : Γ ⊢[PRAAx] distanceBounded (point p E i) (powerValue i) (error E i) (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (point p E (succ i)) (powerValue (succ i)) (error E (succ i)) (unit p) := by
  have current := le_trans (le_succ_self i) hi
  have oneE := le_trans (zero_lt_succ i) hi
  have raw := GaussianNameArithmetic.product_distance (point p E i) (powerValue i) (point p E one) baseValue
    (error E i) two (unit p) (majorant E) (unit E) (unit_positive p) ih (one_error p E oneE)
    (point_bound p E one oneE) (power_bound E i current)
  have right := distance_congr (.eqRefl _) (GaussianRationalReciprocal.power_succ baseValue i).eqSymm (.eqRefl _) (.eqRefl _) raw
  have chain := distance_triangle_same _ _ _ _ _ _ (unit_positive p) (successor_product_error p E i hi) right
  apply distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p) _ chain
  exact le_congr (by unfold stepCost; ipra_ring) (.eqRefl _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (error_growth E i) (le_refl (unit p)))

/-- A guarded QF induction over i<=E holds at the SAME fixed observation p.
There is no induction over regularity, names, or equivalence predicates. -/
theorem prefix_error (p E i : PTm n) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    distanceBounded (point p E i) (powerValue i) (error E i) (unit p) := by
  have hall : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift E) ⟶
      distanceBounded (point (Syn.shift p) (Syn.shift E) (var 0)) (powerValue (var 0))
        (error (Syn.shift E) (var 0)) (unit (Syn.shift p))) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_le, GaussianRationalMetric.subst_distanceBounded, subst_point,
        subst_powerValue, subst_error, GaussianCoefficientNameBounds.subst_unit]
    · exact .impI (error_zero p E)
    · refine .impI ?_
      let IH : Fm PTm (n+1) := le (var 0) (Syn.shift E) ⟶
        distanceBounded (point (Syn.shift p) (Syn.shift E) (var 0)) (powerValue (var 0))
          (error (Syn.shift E) (var 0)) (unit (Syn.shift p))
      let D := le (succ (var 0)) (Syn.shift E) :: IH :: Γ.map Fm.shift
      have old : D ⊢[PRAAx] distanceBounded (point (Syn.shift p) (Syn.shift E) (var 0)) (powerValue (var 0))
          (error (Syn.shift E) (var 0)) (unit (Syn.shift p)) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self (var 0 : PTm (n+1))) Prf.hyp0)
      exact error_step (Syn.shift p) (Syn.shift E) (var 0) Prf.hyp0 old
  have gate : Γ ⊢[PRAAx] le i E ⟶ distanceBounded (point p E i) (powerValue i) (error E i) (unit p) := by
    simpa only [Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,subst_point,subst_powerValue,subst_error,
      GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i
  exact .impE gate hi


theorem final_envelope (E : PTm n) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal expF constantF (expData E E) (powerValue E) (error E E) := by
  refine .allI ?_
  have finite := prefix_error (Γ := Γ.map Fm.shift) (var 0) (Syn.shift E) (Syn.shift E) (le_refl _)
  have actual := distance_congr (.eqRefl _) (GaussianGammaCanonicalExponent.constant_at (var 0) (powerValue (Syn.shift E))).eqSymm
    (.eqRefl _) (.eqRefl _) finite
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianRobinOddExponential.constantF,point,subst_expData,subst_powerValue,subst_error,Syn.shift] using actual

theorem integer_power_cross (E : PTm n) : Γ ⊢[PRAAx] crossEquivalent expF constantF (expData E E) (powerValue E) :=
  GaussianNameRingLaws.equivalent_of_envelope expF constantF (expData E E) (powerValue E) (error E E)
    (point_regular E E (le_refl _)) (GaussianGammaCanonicalExponent.constant_regular _) (final_envelope E)

/-- The actual scaled exponential of the SAME original Robin 1/3 odd
name is the exact natural constant 2^E, for every numerical E including 0. -/
theorem original_Robin_integer_scaled_exponential (E : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianRadiusExponentialName.nameF (GaussianNamedNaturalScale.nameF oddF)) constantF
      (GaussianRadiusExponentialName.data (GaussianNamedNaturalScale.radius E (num 3))
        (GaussianNamedNaturalScale.data E E (GaussianRobinOddLogarithmName.inputs one AnalyticNumberTheory.RobinLogInterval.c3)))
      (GaussianRationalNaturalScale.naturalPoint (pw two E)) :=
  cross_trans _ _ _ _ _ _ (integer_power_cross E)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (power_value_code E))

theorem original_Robin_capped_stage_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (var 0) ⟶ GaussianRadiusExponentialName.input scaledF (radius (var 0)) (stageData (var 0) (var 1))) :=
  closeUniv 2 (.impI (stage_input _ _ Prf.hyp0))
theorem actual_Robin_base_power_code_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (powerValue (var 0) ≐ GaussianRationalNaturalScale.naturalPoint (unit (var 0))) := closeUniv 1 (power_value_code _)
theorem actual_Robin_scaled_zero_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (point (var 0) (var 1) zero ≐ qone) := closeUniv 2 (point_zero _ _)
theorem original_Robin_successor_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (succ (var 1)) (var 0) ⟶ crossEquivalent productF expF (productData (var 0) (var 1)) (expData (var 0) (succ (var 1)))) :=
  closeUniv 2 (.impI (successor_exponential _ _ Prf.hyp0))
theorem original_Robin_numerical_prefix_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 1) ⟶ distanceBounded (point (var 0) (var 1) (var 2)) (powerValue (var 2))
      (error (var 1) (var 2)) (unit (var 0))) := closeUniv 3 (.impI (prefix_error _ _ _ Prf.hyp0))
theorem original_Robin_integer_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent (GaussianRadiusExponentialName.nameF (GaussianNamedNaturalScale.nameF oddF)) constantF
      (GaussianRadiusExponentialName.data (GaussianNamedNaturalScale.radius (var 0) (num 3))
        (GaussianNamedNaturalScale.data (var 0) (var 0) (GaussianRobinOddLogarithmName.inputs one AnalyticNumberTheory.RobinLogInterval.c3)))
      (GaussianRationalNaturalScale.naturalPoint (pw two (var 0)))) :=
  closeUniv 1 (original_Robin_integer_scaled_exponential _)

end LeanProofs.IPRA.Analysis.GaussianRobinIntegerExponential
