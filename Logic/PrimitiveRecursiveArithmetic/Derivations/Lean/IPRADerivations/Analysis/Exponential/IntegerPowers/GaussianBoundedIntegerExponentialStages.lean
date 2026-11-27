import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialAddition
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialMajorant
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallPerturbationTransport
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialInverse
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameEquivalence
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent

/-!
# Actual bounded exponential stages at one numerical cap

The actual capped natural multiple keeps one original input clock at
all stages. Original exponential addition yields the successor law.
Uniform sample and target-power bounds derive its numerical error rule.
Only the original input, original base exponential value and an original
bound for that base value are supplied; no stage law is a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBoundedIntegerExponentialStages

open_ipra
open GaussianRationalHorner (canonical qmul)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_diagonal_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (f : PR 2) (R x c A : PTm n) : Fm PTm n := GaussianRadiusExponentialName.input f R x ⋏
  (crossEquivalent (GaussianRadiusExponentialName.nameF f) constantF (GaussianRadiusExponentialName.data R x) c ⋏ bounded c A one)
def scaledF (f : PR 2) : PR 2 := GaussianNamedNaturalScale.nameF f
def stageData (E i x : PTm n) : PTm n := GaussianNamedNaturalScale.data E i x
def radius (E R : PTm n) : PTm n := GaussianNamedNaturalScale.radius E R
def expF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (scaledF f)
def expData (E i R x : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius E R) (stageData E i x)
def point (f : PR 2) (p E i R x : PTm n) : PTm n := ap2 (expF f) p (expData E i R x)
def majorant (E R : PTm n) : PTm n := pw (num 3) (radius E R)
def powerBudget (E A : PTm n) : PTm n := pw (A+one) E
def productF (f : PR 2) : PR 2 := GaussianNameArithmetic.multiplyF (expF f) (expF f)
def productData (f : PR 2) (E i R x : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyData (expF f) (expF f) (expData E i R x) (expData E one R x)

ipra_subst input
ipra_subst stageData
ipra_subst radius
ipra_subst expData
ipra_subst point
ipra_subst majorant
ipra_subst powerBudget
ipra_subst productData

theorem stage_input (f : PR 2) (E i R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (scaledF f) (radius E R) (stageData E i x) :=
  GaussianNamedNaturalScale.exponential_input f E i R x h.andE₁ hi

theorem point_regular (f : PR 2) (E i R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN (expF f) (expData E i R x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (stage_input f E i R x c A h hi)

theorem point_bound (f : PR 2) (p E i R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx] bounded (point f p E i R x) (majorant E R) one :=
  GaussianRationalReciprocal.bound_congr (GaussianRadiusExponentialName.sample_at _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _ (GaussianRadiusExponentialName.query_bound _ _ _ _
      (stage_input f E i R x c A h hi)))

theorem point_zero (f : PR 2) (p E R x : PTm n) : Γ ⊢[PRAAx] point f p E zero R x ≐ qone :=
  (GaussianRadiusExponentialName.sample_at (scaledF f) (radius E R) p (stageData E zero x)).eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
      (GaussianNamedNaturalScale.sample_zero f _ E x)).eqTrans (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

theorem one_exponential (f : PR 2) (E R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] crossEquivalent (expF f) constantF (expData E one R x) c :=
  cross_trans _ _ _ _ _ _ (GaussianExponentialRadiusIndependence.independent_radii_proper (scaledF f) f
    (radius E R) R (stageData E one x) x (stage_input f E one R x c A h hE) h.andE₁
    (GaussianNamedNaturalScale.one_cross f E R x h.andE₁)) h.andE₂.andE₁

theorem power_bound (c A E i : PTm n) (hc : Γ ⊢[PRAAx] bounded c A one) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    bounded (power c i) (powerBudget E A) one := by
  have grow := GaussianFactorBudget.power_monotone_length (A+one) i E
    (le_congr (.eqRefl _) (add_comm _ _) (le_add_right one A)) hi
  have base : Γ ⊢[PRAAx] bounded c (A+one) one := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (le_refl one) (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) (le_add_right A one)) hc
  have old := GaussianRationalPowerDifference.bounded_power_integer c (A+one) i base
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by unfold powerBudget; ipra_ring) grow) old

theorem successor_exponential (f : PR 2) (E i R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hi : Γ ⊢[PRAAx] le (succ i) E) : Γ ⊢[PRAAx]
    crossEquivalent (productF f) (expF f) (productData f E i R x) (expData E (succ i) R x) := by
  have ii := le_trans (le_succ_self i) hi
  have oneE := le_trans (zero_lt_succ i) hi
  have a := GaussianExponentialAddition.exponential_add_cross (scaledF f) (scaledF f) (radius E R) (stageData E i x) (stageData E one x)
    (GaussianNamedNaturalScale.radius_positive E R) (stage_input f E i R x c A h ii) (stage_input f E one R x c A h oneE)
  have b := GaussianExponentialRadiusIndependence.independent_radii_proper
    (GaussianNameArithmetic.addF (scaledF f) (scaledF f)) (scaledF f) (radius E R+radius E R) (radius E R)
    (GaussianNamedNaturalScale.addData E i x) (stageData E (succ i) x)
    (GaussianExponentialReference.add_input _ _ _ _ _ (stage_input f E i R x c A h ii) (stage_input f E one R x c A h oneE))
    (stage_input f E (succ i) R x c A h hi) (GaussianNamedNaturalScale.add_step_cross f E i R x h.andE₁ hi)
  exact cross_trans _ _ _ _ _ _ a b

theorem one_error (f : PR 2) (p E R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] distanceBounded (point f p E one R x) c two (unit p) := by
  have close := GaussianNameEquivalence.diagonal_at _ _ _ _ p
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (one_exponential f E R x c A h hE))
  exact distance_congr (.eqRefl _) (GaussianGammaCanonicalExponent.constant_at p c) (.eqRefl _) (.eqRefl _) close

theorem later_point_error (f : PR 2) (p q E i R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hi : Γ ⊢[PRAAx] le i E) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    distanceBounded (point f q E i R x) (point f p E i R x) two (unit p) :=
  GaussianNameEquivalence.point_at_later (expF f) (expData E i R x) p q (point_regular f E i R x c A h hi) hpq

theorem product_same_precision (f : PR 2) (p E i R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hi : Γ ⊢[PRAAx] le i E) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (productF f) p (productData f E i R x)) (qmul (point f p E i R x) (point f p E one R x))
      (num 4*majorant E R) (unit p) := by
  let s := GaussianNamedSmallPerturbationTransport.productClock (expF f) (expF f) (expData E i R x) (expData E one R x) p
  have later : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have raw := GaussianNameArithmetic.product_distance (point f s E i R x) (point f p E i R x) (point f s E one R x) (point f p E one R x)
    two two (unit p) (majorant E R) (majorant E R) (unit_positive p)
    (later_point_error f p s E i R x c A h hi later) (later_point_error f p s E one R x c A h hE later)
    (point_bound f s E one R x c A h hE) (point_bound f p E i R x c A h hi)
  exact distance_congr (GaussianNamedSmallPerturbationTransport.product_at (expF f) (expF f) _ _ p).eqSymm
    (.eqRefl _) (by ipra_ring) (.eqRefl _) raw

theorem successor_product_error (f : PR 2) (p E i R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hi : Γ ⊢[PRAAx] le (succ i) E) : Γ ⊢[PRAAx]
    distanceBounded (point f p E (succ i) R x) (qmul (point f p E i R x) (point f p E one R x))
      (two+num 4*majorant E R) (unit p) := by
  have closer := distance_symmetric _ _ _ _ (unit_positive p)
    (cross_diagonal_at p (successor_exponential f E i R x c A h hi))
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) closer
    (product_same_precision f p E i R x c A h (le_trans (le_succ_self i) hi) (le_trans (zero_lt_succ i) hi))

theorem actual_bounded_integer_stage_input_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input f (var 2) (var 3) (var 4) (var 5) ⟶ le (var 1) (var 0) ⟶
      GaussianRadiusExponentialName.input (scaledF f) (radius (var 0) (var 2)) (stageData (var 0) (var 1) (var 3))) :=
  closeUniv 6 (.impI (.impI (stage_input f _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_integer_power_fixed_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 0) (var 1) one ⟶ le (var 3) (var 2) ⟶
      bounded (power (var 0) (var 3)) (powerBudget (var 2) (var 1)) one) :=
  closeUniv 4 (.impI (.impI (power_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_bounded_integer_successor_exponential_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input f (var 2) (var 3) (var 4) (var 5) ⟶ le (succ (var 1)) (var 0) ⟶
      crossEquivalent (productF f) (expF f) (productData f (var 0) (var 1) (var 2) (var 3))
        (expData (var 0) (succ (var 1)) (var 2) (var 3))) :=
  closeUniv 6 (.impI (.impI (successor_exponential f _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_bounded_integer_successor_sample_error_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input f (var 3) (var 4) (var 5) (var 6) ⟶ le (succ (var 2)) (var 1) ⟶
      distanceBounded (point f (var 0) (var 1) (succ (var 2)) (var 3) (var 4))
        (qmul (point f (var 0) (var 1) (var 2) (var 3) (var 4)) (point f (var 0) (var 1) one (var 3) (var 4)))
        (two+num 4*majorant (var 1) (var 3)) (unit (var 0))) :=
  closeUniv 7 (.impI (.impI (successor_product_error f _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBoundedIntegerExponentialStages
