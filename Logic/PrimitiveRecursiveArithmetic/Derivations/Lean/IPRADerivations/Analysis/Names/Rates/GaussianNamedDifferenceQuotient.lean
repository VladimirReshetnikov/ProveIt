import IPRADerivations.Analysis.Names.GaussianNamedDifference
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalLowerBounds
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSlackRemoval
import IPRADerivations.Analysis.Names.GaussianBoundedConstantProductName

/-!
# Actual divided differences of two original regular names

The numerator is the literal left-minus-right name. A fixed original
reciprocal of the nonzero native increment multiplies that name. The
original programs, their real multiplication clocks and the three
independent observation queries remain visible throughout.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDifferenceQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalReciprocal (reciprocal bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def separated (h D : PTm n) : Fm PTm n := le one D ⋏ le one (ComplexLogarithmRemainder.normSq h)
def inverse (h D : PTm n) : PTm n := reciprocal (ofGaussian h D)
def nameF (f g : PR 2) : PR 2 := multiplyF constantF (GaussianNamedDifference.nameF f g)
def data (f g : PR 2) (x y h D : PTm n) : PTm n :=
  multiplyData constantF (GaussianNamedDifference.nameF f g) (inverse h D) (GaussianNamedDifference.data x y)
def input (f g : PR 2) (x y h D : PTm n) : Fm PTm n := pointCN f x ⋏ (pointCN g y ⋏ separated h D)
def raw (f g : PR 2) (q r x y h D : PTm n) : PTm n := qmul (inverse h D) (qsub (ap2 f q x) (ap2 g r y))
def cost (f g : PR 2) (x y h D : PTm n) : PTm n :=
  multiplyModulus constantF (GaussianNamedDifference.nameF f g) (inverse h D) (GaussianNamedDifference.data x y)+one+num 6*D
def numerator (D p q r : PTm n) : PTm n := unit q*unit r+D*unit p*(unit q+unit r)
def denominator (p q r : PTm n) : PTm n := unit p*unit q*unit r

@[simp] theorem subst_separated {m : ℕ} (σ : Fin n → PTm m) (h D : PTm n) :
    (separated h D).subst σ = separated (Syn.subst σ h) (Syn.subst σ D) := by simp [separated]
@[simp] theorem subst_inverse {m : ℕ} (σ : Fin n → PTm m) (h D : PTm n) :
    Syn.subst σ (inverse h D) = inverse (Syn.subst σ h) (Syn.subst σ D) := by simp [inverse]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y h D : PTm n) :
    Syn.subst σ (data f g x y h D) = data f g (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ h) (Syn.subst σ D) := by simp [data]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y h D : PTm n) :
    (input f g x y h D).subst σ = input f g (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ h) (Syn.subst σ D) := by simp [input]
@[simp] theorem subst_raw {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (q r x y h D : PTm n) :
    Syn.subst σ (raw f g q r x y h D) = raw f g (Syn.subst σ q) (Syn.subst σ r)
      (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ h) (Syn.subst σ D) := by simp [raw]
@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y h D : PTm n) :
    Syn.subst σ (cost f g x y h D) = cost f g (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ h) (Syn.subst σ D) := by simp [cost]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (D p q r : PTm n) :
    Syn.subst σ (numerator D p q r) = numerator (Syn.subst σ D) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ r) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p q r : PTm n) :
    Syn.subst σ (denominator p q r) = denominator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ r) := by simp [denominator]

theorem parameter_lower (h D : PTm n) (hs : Γ ⊢[PRAAx] separated h D) : Γ ⊢[PRAAx]
    GaussianNameReciprocal.lower (ofGaussian h D) D :=
  GaussianRationalLowerBounds.lower_from_representation _ _ D one D hs.andE₁ hs.andE₁
    (GaussianRationalHorner.ofGaussian_represents h D hs.andE₁)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (D*D) hs.andE₂))

theorem inverse_bound (h D : PTm n) (hs : Γ ⊢[PRAAx] separated h D) : Γ ⊢[PRAAx]
    bounded (inverse h D) D one := GaussianNameReciprocal.inverse_bound _ D hs.andE₁ (parameter_lower h D hs)

theorem actual_inverse (h D : PTm n) (hs : Γ ⊢[PRAAx] separated h D) : Γ ⊢[PRAAx]
    qmul (inverse h D) (ofGaussian h D) ≐ GaussianRationalSyntheticDivision.qone :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    (GaussianRationalReciprocal.reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ D hs.andE₁ (parameter_lower h D hs)))

theorem name_regular (f g : PR 2) (x y h D : PTm n) (hs : Γ ⊢[PRAAx] input f g x y h D) : Γ ⊢[PRAAx]
    pointCN (nameF f g) (data f g x y h D) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianNamedDifference.name_regular f g x y hs.andE₁ hs.andE₂.andE₁)

theorem scale_distance (a u v K A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] bounded a K one) (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    distanceBounded (qmul a u) (qmul a v) (K*A) B :=
  bound_congr (GaussianRationalRoundedPower.multiplication_difference a u v).eqSymm (.eqRefl _) (one_mul _)
    (bounded_product _ _ K one A B (le_refl one) hB ha hd)

theorem sample_error (f g : PR 2) (p x y h D : PTm n) (hs : Γ ⊢[PRAAx] input f g x y h D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f g) p (data f g x y h D)) (raw f g p p x y h D) (cost f g x y h D) (unit p) := by
  have diff := GaussianNamedDifference.name_regular f g x y hs.andE₁ hs.andE₂.andE₁
  have first := distance_congr (.eqRefl _)
    (GaussianRationalSyntheticDivision.qmul_congr (constant_at p (inverse h D)) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF (GaussianNamedDifference.nameF f g)
      (inverse h D) (GaussianNamedDifference.data x y) p (constant_regular _) diff)
  have second := scale_distance (inverse h D) _ _ D (num 6) (unit p) (unit_positive p)
    (inverse_bound h D hs.andE₂.andE₂) (GaussianNamedDifference.sample_error f g x y p hs.andE₁ hs.andE₂.andE₁)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold cost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second)

theorem denominator_positive (p q r : PTm n) : Γ ⊢[PRAAx] le one (denominator p q r) :=
  positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive r)

theorem observation_slack (f g : PR 2) (p q r t x y h D : PTm n) (hs : Γ ⊢[PRAAx] input f g x y h D) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 (nameF f g) p (data f g x y h D)) (raw f g q r x y h D))
      (numerator D p q r) (denominator p q r) (cost f g x y h D+one+two*D) t := by
  let Z := denominator p q r*unit t
  have hz : Γ ⊢[PRAAx] le one Z := positive_product _ _ (denominator_positive p q r) (unit_positive t)
  have first := distance_radius_mono _ _ _ _ ((unit p+unit t)*(unit q*unit r)) Z
    (positive_product _ _ (unit_positive p) (unit_positive t)) hz
    (le_of_eq_add (d := zero) (by dsimp only [Z,denominator]; ipra_ring))
    (GaussianNameEquivalence.point_at (nameF f g) (data f g x y h D) p t (name_regular f g x y h D hs))
  have second := distance_radius_mono _ _ _ _ (cost f g x y h D*(unit p*unit q*unit r)) Z (unit_positive t) hz
    (le_of_eq_add (d := zero) (by dsimp only [Z,denominator]; ipra_ring)) (sample_error f g t x y h D hs)
  have left := distance_radius_mono _ _ _ _ ((unit t+unit q)*(unit p*unit r)) Z
    (positive_product _ _ (unit_positive t) (unit_positive q)) hz
    (le_of_eq_add (d := zero) (by dsimp only [Z,denominator]; ipra_ring)) (GaussianNameEquivalence.point_at f x t q hs.andE₁)
  have right := distance_radius_mono _ _ _ _ ((unit t+unit r)*(unit p*unit q)) Z
    (positive_product _ _ (unit_positive t) (unit_positive r)) hz
    (le_of_eq_add (d := zero) (by dsimp only [Z,denominator]; ipra_ring)) (GaussianNameEquivalence.point_at g y t r hs.andE₂.andE₁)
  have last := scale_distance (inverse h D) _ _ D _ Z hz (inverse_bound h D hs.andE₂.andE₂)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hz left right)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [numerator,denominator,unit]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hz first (distance_triangle_same _ _ _ _ _ _ hz second last))

def gapQuery (f g : PR 2) (p q r x y h D : PTm n) : PTm n :=
  GaussianRationalSlackRemoval.precision (qsub (ap2 (nameF f g) p (data f g x y h D)) (raw f g q r x y h D))
    (numerator D p q r) (denominator p q r) (cost f g x y h D+one+two*D)

theorem independent_readback (f g : PR 2) (p q r x y h D : PTm n) (hs : Γ ⊢[PRAAx] input f g x y h D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f g) p (data f g x y h D)) (raw f g q r x y h D)
      (numerator D p q r) (denominator p q r) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (cost f g x y h D+one+two*D) (denominator_positive p q r)
    (observation_slack f g p q r (gapQuery f g p q r x y h D) x y h D hs)

theorem actual_native_increment_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (separated (var 0) (var 1) ⟶ qmul (inverse (var 0) (var 1)) (ofGaussian (var 0) (var 1)) ≐ GaussianRationalSyntheticDivision.qone) :=
  closeUniv 2 (.impI (actual_inverse _ _ Prf.hyp0))

theorem actual_original_divided_difference_independent_readback_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input f g (var 0) (var 1) (var 2) (var 3) ⟶
      (pointCN (nameF f g) (data f g (var 0) (var 1) (var 2) (var 3)) ⋏
       distanceBounded (ap2 (nameF f g) (var 4) (data f g (var 0) (var 1) (var 2) (var 3)))
         (raw f g (var 5) (var 6) (var 0) (var 1) (var 2) (var 3))
         (numerator (var 3) (var 4) (var 5) (var 6)) (denominator (var 4) (var 5) (var 6)))) :=
  closeUniv 7 (.impI (.andI (name_regular f g _ _ _ _ Prf.hyp0) (independent_readback f g _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedDifferenceQuotient
