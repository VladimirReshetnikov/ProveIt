import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalCircleParametrization
import IPRADerivations.Analysis.Polynomials.RootFinding.RationalSquareRootBounds
import IPRADerivations.Analysis.Geometry.GaussianRelativeNormTriangle
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalL1
import IPRADerivations.Analysis.RationalArithmetic.GaussianIntegerCircleProjection
import IPRADerivations.Combinatorics.FiniteBijection
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerDifference
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianReconstructionRoots
import IPRADerivations.Core.LinearCombination

/-!
# An actual principal rational half-angle step

The sign branch is strictly negative, with zero taking the positive sign.
Integer square-root floors feed an exact rational circle parametrization.
The input point and precision denominator are numerical object variables;
the unit guard supplies the coordinate and square-root bounds internally.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHalfAngle

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im code normSq normSq_eval)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (represents positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq qsub)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (positivePart)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq zabs_neg)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def unit (q : PTm n) : Fm PTm n := qnormSq q ≐ fraction one one
def base (q : PTm n) : PTm n := two*rawDen q
def plus (q : PTm n) : PTm n := positivePart (ZT.ofNat (rawDen q)+re (rawGaussian q))
def minus (q : PTm n) : PTm n := positivePart (ZT.ofNat (rawDen q)-re (rawGaussian q))
def negativeBit (q : PTm n) : PTm n := sg (monus (im (rawGaussian q)).neg (im (rawGaussian q)).pos)
def grid (q H : PTm n) : PTm n := base q*H
def plusRoot (q H : PTm n) : PTm n := RationalSquareRootBounds.root (plus q) (base q) H
def minusRoot (q H : PTm n) : PTm n := RationalSquareRootBounds.root (minus q) (base q) H
def circleL (q H : PTm n) : PTm n := grid q H+plusRoot q H
def half (q H : PTm n) : PTm n :=
  GaussianRationalCircleParametrization.point (circleL q H) (minusRoot q H) (negativeBit q)

@[simp] theorem subst_unit {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    (unit q).subst σ = unit (Syn.subst σ q) := by simp [unit]
@[simp] theorem subst_base {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (base q) = base (Syn.subst σ q) := by simp [base]
@[simp] theorem subst_plus {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (plus q) = plus (Syn.subst σ q) := by simp [plus]
@[simp] theorem subst_minus {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (minus q) = minus (Syn.subst σ q) := by simp [minus]
@[simp] theorem subst_negativeBit {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (negativeBit q) = negativeBit (Syn.subst σ q) := by simp [negativeBit,ComplexLogarithmRemainder.im,ZT.subst]
@[simp] theorem subst_grid {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (grid q H) = grid (Syn.subst σ q) (Syn.subst σ H) := by simp [grid]
@[simp] theorem subst_plusRoot {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (plusRoot q H) = plusRoot (Syn.subst σ q) (Syn.subst σ H) := by simp [plusRoot]
@[simp] theorem subst_minusRoot {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (minusRoot q H) = minusRoot (Syn.subst σ q) (Syn.subst σ H) := by simp [minusRoot]
@[simp] theorem subst_circleL {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (circleL q H) = circleL (Syn.subst σ q) (Syn.subst σ H) := by simp [circleL]
@[simp] theorem subst_half {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (half q H) = half (Syn.subst σ q) (Syn.subst σ H) := by simp [half]

theorem negative_bit_boolean (q : PTm n) : Γ ⊢[PRAAx]
    (negativeBit q ≐ zero) ⋎ (negativeBit q ≐ one) := Combinatorics.FiniteBijection.sg_bit _

theorem base_positive (q : PTm n) : Γ ⊢[PRAAx] le one (base q) :=
  positive_product _ _ (le_of_eq_add (d := one) (by ipra_ring)) (raw_den_positive q)

theorem grid_positive (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx] le one (grid q H) :=
  positive_product _ _ (base_positive q) hH

theorem circleL_positive (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx] le one (circleL q H) :=
  le_trans (grid_positive q H hH) (le_add_right _ _)

theorem half_unit (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx] unit (half q H) :=
  GaussianRationalCircleParametrization.unit_norm _ _ _ (circleL_positive q H hH) (negative_bit_boolean q)

theorem half_canonical (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (half q H) :=
  GaussianRationalCircleParametrization.point_canonical _ _ _ (circleL_positive q H hH)

theorem raw_unit (q : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    normSq (rawGaussian q) ≐ rawDen q*rawDen q := by
  have hn := GaussianRationalMetric.qnormSq_represents (Γ := Γ) q (rawGaussian q) (rawDen q)
    (raw_den_positive q) (raw_represents q)
  have ho := fraction_represents (Γ := Γ) one one (le_refl one)
  have forward : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq q) (fraction one one) :=
    RationalArgmin.rationalLE_congr h.eqSymm (.eqRefl _) (RationalArgmin.reflexive _)
  have backward : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fraction one one) (qnormSq q) :=
    RationalArgmin.rationalLE_congr (.eqRefl _) h.eqSymm (RationalArgmin.reflexive _)
  have f := GaussianRationalMetric.comparison_to_cleared (qnormSq q) (fraction one one) (normSq (rawGaussian q)) one (rawDen q*rawDen q) one hn ho forward
  have b := GaussianRationalMetric.comparison_to_cleared (fraction one one) (qnormSq q) one (normSq (rawGaussian q)) one (rawDen q*rawDen q) ho hn backward
  exact le_antisymm (le_congr (by ipra_ring) (by ipra_ring) f) (le_congr (by ipra_ring) (by ipra_ring) b)

theorem real_absolute_bound (q : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (zabs (re (rawGaussian q))) (rawDen q) :=
  nat_sqrt_mono (le_trans (le_add_right _ _) (le_congr (.eqRefl _) (raw_unit q h) (le_refl _)))

theorem signed_absolute_order (a : ZT n) : Γ ⊢[PRAAx] le a.neg (zabs a+a.pos) := by
  have h := GaussianRelativeNormTriangle.signed_le_absolute (Γ := Γ) (-a)
  exact le_congr (add_zero _) (congrAdd (zabs_neg a) (.eqRefl _)) h

theorem positive_part_value (a : ZT n) (h : Γ ⊢[PRAAx] le a.neg a.pos) :
    ZT.toZ Γ (ZT.ofNat (positivePart a)) = ZT.toZ Γ a := by
  have e := natEq (eq_add_of_le h)
  rw [ZT.toZ_ofNat]
  change 𝔞(positivePart a) = 𝔞(a.pos)-𝔞(a.neg)
  unfold positivePart
  ipra_simps
  linear_combination -e

theorem plus_value (q : PTm n) (h : Γ ⊢[PRAAx] unit q) :
    𝔞(plus q) = 𝔞(rawDen q)+ZT.toZ Γ (re (rawGaussian q)) := by
  have b := le_trans (signed_absolute_order (Γ := Γ) (re (rawGaussian q)))
    (add_le_add_right _ (real_absolute_bound q h))
  have p := positive_part_value (Γ := Γ) (ZT.ofNat (rawDen q)+re (rawGaussian q))
    (le_congr (zero_add _).eqSymm (.eqRefl _) b)
  simpa only [plus,ZT.toZ_ofNat,ZT.toZ_add] using p

theorem minus_value (q : PTm n) (h : Γ ⊢[PRAAx] unit q) :
    𝔞(minus q) = 𝔞(rawDen q)-ZT.toZ Γ (re (rawGaussian q)) := by
  have b := le_trans (signed_absolute_order (Γ := Γ) (-re (rawGaussian q)))
    (add_le_add_right _ (le_congr (zabs_neg _).eqSymm (.eqRefl _) (real_absolute_bound q h)))
  have p := positive_part_value (Γ := Γ) (ZT.ofNat (rawDen q)-re (rawGaussian q))
    (le_congr (zero_add _).eqSymm (.eqRefl _) b)
  simpa only [minus,ZT.toZ_ofNat,ZT.toZ_sub] using p

theorem plus_minus_sum (q : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    plus q+minus q ≐ base q := by
  have p := plus_value q h
  have m := minus_value q h
  apply deriveNat
  unfold base
  ipra_simps
  linear_combination p+m

theorem plus_bound (q : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx] le (plus q) (base q) :=
  le_congr (.eqRefl _) (plus_minus_sum q h) (le_add_right _ _)

theorem minus_bound (q : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx] le (minus q) (base q) :=
  le_congr (.eqRefl _) (plus_minus_sum q h) (le_add_left _ _)

theorem plus_root_bound (q H : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (plusRoot q H) (grid q H) :=
  RationalSquareRootBounds.root_unit_bound _ _ _ (plus_bound q h)

theorem minus_root_bound (q H : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (minusRoot q H) (grid q H) :=
  RationalSquareRootBounds.root_unit_bound _ _ _ (minus_bound q h)

theorem plus_root_lower (q H : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (plus q*H) (plusRoot q H) :=
  RationalSquareRootBounds.root_scaled_lower _ _ _ (plus_bound q h)

theorem half_real_nonnegative (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fraction zero one) (fstT (half q H)) :=
  GaussianRationalCircleParametrization.real_nonnegative_order _ _ _ (circleL_positive q H hH)
    (le_trans (minus_root_bound q H h) (le_add_right _ _))

theorem input_distance_numerator (q : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    normSq (GaussianRootAlgebra.sub (rawGaussian q)
      (ComplexLogarithmRemainder.scale (rawDen q) ComplexLogarithmRemainder.oneCode)) ≐
      two*rawDen q*minus q := by
  have un := natEq (raw_unit q h)
  have mv := minus_value q h
  apply deriveNat
  rw [normSq_eval]
  simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
    GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  rw [normSq_eval] at un
  ipra_simps
  linear_combination un-2*𝔞(rawDen q)*mv

theorem input_distance (q : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    qnormSq (qsub q GaussianRationalReciprocal.qone) ≐ fraction (two*minus q) (rawDen q) := by
  have hD := raw_den_positive (Γ := Γ) q
  have difference := GaussianRationalMetric.qsub_represents (Γ := Γ) _ _ _ _ _ hD
    (raw_represents q) (GaussianRationalReciprocal.qone_represents_scaled _)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalMetric.qnormSq_canonical _)
    (RationalNormalForm.normalize_well_formed _ _ hD)
    (GaussianRationalMetric.qnormSq_represents _ _ _ hD difference)
    (fraction_represents _ _ hD) (positive_product _ _ hD hD) hD
  apply ZT.derive
  have e := natEq (input_distance_numerator q h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  rw [e]
  ring

theorem contraction_cleared (q H : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (GaussianRationalCircleParametrization.four*rawDen q*minusRoot q H*minusRoot q H)
      (minus q*GaussianRationalCircleParametrization.denominator (circleL q H) (minusRoot q H)) := by
  have leftBound : Γ ⊢[PRAAx] le ((base q+plus q)*H) (circleL q H) :=
    le_congr (by unfold grid; ipra_ring) (by unfold circleL; ipra_ring) (add_le_add_right (grid q H) (plus_root_lower q H h))
  have productBound := le_mul_mono (le_add_right (grid q H) (plusRoot q H)) leftBound
  have rootBound := RationalSquareRootBounds.root_lower (Γ := Γ) (minus q) (base q) H
  have scaledRoot : Γ ⊢[PRAAx] le ((base q+plus q)*(minusRoot q H*minusRoot q H))
      ((base q+plus q)*RationalSquareRootBounds.radicand (minus q) (base q) H) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (base q+plus q) rootBound)
  have scaledProduct : Γ ⊢[PRAAx] le
      ((base q+plus q)*RationalSquareRootBounds.radicand (minus q) (base q) H)
      (minus q*(circleL q H*circleL q H)) :=
    le_congr (by unfold RationalSquareRootBounds.radicand grid; ipra_ring)
      (by unfold circleL; ipra_ring) (mul_le_mul_right (minus q) productBound)
  have upper := le_trans scaledRoot scaledProduct
  have combined := add_le_add₂ upper (le_refl (minus q*minusRoot q H*minusRoot q H))
  have sum := natEq (plus_minus_sum q h)
  apply le_congr (b' := minus q*GaussianRationalCircleParametrization.denominator (circleL q H) (minusRoot q H)) ?_ ?_ combined
  · apply deriveNat
    unfold base at sum
    unfold base GaussianRationalCircleParametrization.four
    ipra_simps
    linear_combination 𝔞(minusRoot q H)*𝔞(minusRoot q H)*sum
  · unfold GaussianRationalCircleParametrization.denominator
    ipra_ring

theorem half_contraction_fraction (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (qsub (half q H) GaussianRationalReciprocal.qone))
      (fraction (minus q) (rawDen q)) := by
  have hW := GaussianRationalCircleParametrization.denominator_positive (Γ := Γ) (circleL q H) (minusRoot q H) (circleL_positive q H hH)
  have distance := GaussianRationalCircleParametrization.distance_one (Γ := Γ) (circleL q H) (minusRoot q H) (negativeBit q)
    (circleL_positive q H hH) (negative_bit_boolean q)
  apply RationalArgmin.rationalLE_congr distance.eqSymm (.eqRefl _)
  apply GaussianEuclideanDistanceName.fraction_order _ _ _ _ hW (raw_den_positive q)
  exact le_congr (by ipra_ring) (.eqRefl _) (contraction_cleared q H h)

def plusDeficit (q H : PTm n) : PTm n := RationalSquareRootBounds.deficit (plus q) (base q) H
def minusDeficit (q H : PTm n) : PTm n := RationalSquareRootBounds.deficit (minus q) (base q) H
def deficit (q H : PTm n) : PTm n := plusDeficit q H+minusDeficit q H
def floorNumerator (q H : PTm n) : PTm n := code (ZT.ofNat (plusRoot q H))
  (ZT.ofNat (minusRoot q H)-ZT.ofNat (two*negativeBit q*minusRoot q H))
def floorPoint (q H : PTm n) : PTm n := GaussianRationalHorner.ofGaussian (floorNumerator q H) (grid q H)
def circleDen (q H : PTm n) : PTm n := GaussianRationalCircleParametrization.denominator (circleL q H) (minusRoot q H)
def circleNumerator (q H : PTm n) : PTm n := GaussianRationalCircleParametrization.numerator (circleL q H) (minusRoot q H) (negativeBit q)

@[simp] theorem subst_plusDeficit {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (plusDeficit q H) = plusDeficit (Syn.subst σ q) (Syn.subst σ H) := by simp [plusDeficit]
@[simp] theorem subst_minusDeficit {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (minusDeficit q H) = minusDeficit (Syn.subst σ q) (Syn.subst σ H) := by simp [minusDeficit]
@[simp] theorem subst_deficit {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (deficit q H) = deficit (Syn.subst σ q) (Syn.subst σ H) := by simp [deficit]
@[simp] theorem subst_floorNumerator {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (floorNumerator q H) = floorNumerator (Syn.subst σ q) (Syn.subst σ H) := by simp [floorNumerator]
@[simp] theorem subst_floorPoint {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (floorPoint q H) = floorPoint (Syn.subst σ q) (Syn.subst σ H) := by simp [floorPoint]
@[simp] theorem subst_circleDen {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (circleDen q H) = circleDen (Syn.subst σ q) (Syn.subst σ H) := by simp [circleDen]
@[simp] theorem subst_circleNumerator {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (circleNumerator q H) = circleNumerator (Syn.subst σ q) (Syn.subst σ H) := by simp [circleNumerator]

theorem roots_deficit (q H : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    plusRoot q H*plusRoot q H+minusRoot q H*minusRoot q H+deficit q H ≐ grid q H*grid q H := by
  unfold plusRoot minusRoot deficit plusDeficit minusDeficit grid
  ipra_lc [RationalSquareRootBounds.radicand, base] natEq (RationalSquareRootBounds.root_deficit (Γ := Γ) (plus q) (base q) H)+
    natEq (RationalSquareRootBounds.root_deficit (Γ := Γ) (minus q) (base q) H)+
    2*𝔞(rawDen q)*𝔞(H)*𝔞(H)*natEq (plus_minus_sum q h)

theorem deficit_bound (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (deficit q H) ((two*RationalSquareRootBounds.three)*grid q H) :=
  le_congr (.eqRefl _) (by unfold grid RationalSquareRootBounds.denominator; ipra_ring)
    (add_le_add₂ (RationalSquareRootBounds.deficit_bound _ _ _ (base_positive q) hH (plus_bound q h))
      (RationalSquareRootBounds.deficit_bound _ _ _ (base_positive q) hH (minus_bound q h)))

theorem negative_bit_square (q : PTm n) : Γ ⊢[PRAAx] negativeBit q*negativeBit q ≐ negativeBit q := by
  refine .orE (negative_bit_boolean q) ?_ ?_
  · exact (congrMul Prf.hyp0 Prf.hyp0).eqTrans ((zero_mul _).eqTrans Prf.hyp0.eqSymm)
  · exact (congrMul Prf.hyp0 Prf.hyp0).eqTrans ((one_mul _).eqTrans Prf.hyp0.eqSymm)

theorem negative_bit_sign (q : PTm n) :
    ZT.toZ Γ (im (rawGaussian q))-𝔞(two*negativeBit q)*ZT.toZ Γ (im (rawGaussian q)) =
      𝔞(zabs (im (rawGaussian q))) := by
  let y := im (rawGaussian q)
  have result : Γ ⊢[PRAAx] ZT.eq (y-ZT.ofNat (two*negativeBit q)*y) (ZT.ofNat (zabs y)) := by
    refine .orE (lt_or_le y.pos y.neg) ?_ ?_
    · have b := natEq (AnalyticNumberTheory.Totatives.sg_lt (Prf.hyp0 : (lt y.pos y.neg)::Γ ⊢[PRAAx] _))
      have ord := le_of_lt (Prf.hyp0 : (lt y.pos y.neg)::Γ ⊢[PRAAx] _)
      have e := natEq (eq_add_of_le ord)
      apply ZT.derive
      change _ = _ at b
      simp only [ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
      simp only [ZT.toZ]
      unfold zabs Probability.Variance.ad
      unfold negativeBit
      change _ = _ at b
      ipra_simps
      have z := natEq ord
      ipra_simps
      linear_combination -2*(𝔞(y.pos)-𝔞(y.neg))*b+e-z
    · have b := natEq (AnalyticNumberTheory.Totatives.sg_le (Prf.hyp0 : (le y.neg y.pos)::Γ ⊢[PRAAx] _))
      have e := natEq (eq_add_of_le (Prf.hyp0 : (le y.neg y.pos)::Γ ⊢[PRAAx] _))
      apply ZT.derive
      simp only [ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
      simp only [ZT.toZ]
      unfold zabs Probability.Variance.ad
      unfold negativeBit
      change _ = _ at b
      ipra_simps
      have z := natEq (Prf.hyp0 : (le y.neg y.pos)::Γ ⊢[PRAAx] _)
      ipra_simps
      linear_combination -2*(𝔞(y.pos)-𝔞(y.neg))*b+e-z
  have e := ZT.toZ_eq result
  simpa only [ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat,y] using e

theorem floor_numerator_norm (q H : PTm n) : Γ ⊢[PRAAx]
    normSq (floorNumerator q H) ≐ plusRoot q H*plusRoot q H+minusRoot q H*minusRoot q H := by
  have b := natEq (negative_bit_square (Γ := Γ) q)
  apply deriveNat
  rw [floorNumerator,ComplexLogarithmRemainder.normSq_code]
  simp only [ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  linear_combination 4*𝔞(minusRoot q H)*𝔞(minusRoot q H)*b

theorem floor_bounded (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (floorPoint q H) one one := by
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (grid_positive q H hH) (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents _ _ (grid_positive q H hH))
  have bound := le_congr (.eqRefl _) (roots_deficit q H h) (le_add_right _ (deficit q H))
  exact le_congr (by ipra_ring) (by ipra_ring) (le_congr (floor_numerator_norm q H).eqSymm (.eqRefl _) bound)

theorem imaginary_product (q : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    plus q*minus q ≐ zabs (im (rawGaussian q))*zabs (im (rawGaussian q)) := by
  have p := plus_value q h
  have m := minus_value q h
  have un := natEq (raw_unit q h)
  rw [normSq_eval] at un
  apply deriveNat
  simp only [Q.mk_mul,map_mul]
  have ay := zabs_sq (Γ := Γ) (im (rawGaussian q))
  rw [p,m]
  ipra_simps
  linear_combination -un-ay

theorem imaginary_root_order (q H : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (two*rawDen q*plusRoot q H*minusRoot q H)
      (grid q H*grid q H*zabs (im (rawGaussian q))) := by
  have prod := le_mul_mono (RationalSquareRootBounds.root_lower (Γ := Γ) (plus q) (base q) H)
    (RationalSquareRootBounds.root_lower (Γ := Γ) (minus q) (base q) H)
  have product := natEq (imaginary_product q h)
  apply nat_sqrt_mono
  apply le_congr (b' := (grid q H*grid q H*zabs (im (rawGaussian q)))*(grid q H*grid q H*zabs (im (rawGaussian q))))
    (by unfold plusRoot minusRoot base; ipra_ring) ?_ (mul_le_mul_right (base q*base q) prod)
  apply deriveNat
  unfold RationalSquareRootBounds.radicand grid
  ipra_simps
  linear_combination 𝔞(base q)^4*𝔞(H)^4*product

theorem ad_square_gap (a b : PTm n) (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    le (Probability.Variance.ad a b*Probability.Variance.ad a b+b*b) (a*a) := by
  refine le_of_eq_add (d := two*b*monus a b) ?_
  ipra_lc -natEq (Probability.Variance.ad_sq (Γ := Γ) a b)+2*𝔞(b)*natEq (eq_add_of_le h)

def floorSquareDifference (q H : PTm n) : PTm n := GaussianRootAlgebra.sub
  (ComplexLogarithmRemainder.scale (rawDen q) (ComplexLogarithmRemainder.mul (floorNumerator q H) (floorNumerator q H)))
  (ComplexLogarithmRemainder.scale (grid q H*grid q H) (rawGaussian q))

theorem floor_square_difference_norm (q H : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    normSq (floorSquareDifference q H) ≐
      (rawDen q*rawDen q)*(Probability.Variance.ad (plusDeficit q H) (minusDeficit q H)*Probability.Variance.ad (plusDeficit q H) (minusDeficit q H))+
      Probability.Variance.ad (grid q H*grid q H*zabs (im (rawGaussian q))) (two*rawDen q*plusRoot q H*minusRoot q H)*
        Probability.Variance.ad (grid q H*grid q H*zabs (im (rawGaussian q))) (two*rawDen q*plusRoot q H*minusRoot q H) := by
  have rp := natEq (RationalSquareRootBounds.root_deficit (Γ := Γ) (plus q) (base q) H)
  have rm := natEq (RationalSquareRootBounds.root_deficit (Γ := Γ) (minus q) (base q) H)
  have bs := natEq (negative_bit_square (Γ := Γ) q)
  have sign := negative_bit_sign (Γ := Γ) q
  have pv := plus_value q h
  have mv := minus_value q h
  have ap := natEq (Probability.Variance.ad_sq (Γ := Γ) (plusDeficit q H) (minusDeficit q H))
  have ai := natEq (Probability.Variance.ad_sq (Γ := Γ)
    (grid q H*grid q H*zabs (im (rawGaussian q))) (two*rawDen q*plusRoot q H*minusRoot q H))
  apply deriveNat
  rw [normSq_eval]
  unfold floorSquareDifference
  simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul]
  simp only [floorNumerator,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
    ZT.toZ_sub,ZT.toZ_ofNat]
  have absY := zabs_sq (Γ := Γ) (im (rawGaussian q))
  simp only [plusDeficit,minusDeficit,plusRoot,minusRoot,RationalSquareRootBounds.radicand,grid,base] at rp rm ap ai ⊢
  ipra_simps
  -- Rewrite the two signed coordinate squares through their actual gaps.
  have realGap : 𝔞(rawDen q)*(𝔞(RationalSquareRootBounds.root (plus q) (two*rawDen q) H)^2-
      (𝔞(RationalSquareRootBounds.root (minus q) (two*rawDen q) H)-2*𝔞(negativeBit q)*𝔞(RationalSquareRootBounds.root (minus q) (two*rawDen q) H))^2)-
      (2*𝔞(rawDen q)*𝔞(H))^2*ZT.toZ Γ (re (rawGaussian q)) =
      𝔞(rawDen q)*(𝔞(RationalSquareRootBounds.deficit (minus q) (two*rawDen q) H)-𝔞(RationalSquareRootBounds.deficit (plus q) (two*rawDen q) H)) := by
    linear_combination 𝔞(rawDen q)*rp-𝔞(rawDen q)*rm+
      2*𝔞(rawDen q)^2*𝔞(H)^2*pv-2*𝔞(rawDen q)^2*𝔞(H)^2*mv-
      4*𝔞(rawDen q)*𝔞(RationalSquareRootBounds.root (minus q) (two*rawDen q) H)^2*bs
  have realSquare := congrArg (fun z => z*z) realGap
  have bs1 : (1-2*Groth.ι (Q.mk Γ (negativeBit q)))^2=1 := by linear_combination 4*bs
  have isq : (2*𝔞(rawDen q)*𝔞(RationalSquareRootBounds.root (plus q) (two*rawDen q) H)*
      (𝔞(RationalSquareRootBounds.root (minus q) (two*rawDen q) H)-2*𝔞(negativeBit q)*𝔞(RationalSquareRootBounds.root (minus q) (two*rawDen q) H))-
      (2*𝔞(rawDen q)*𝔞(H))^2*ZT.toZ Γ (im (rawGaussian q)))^2 =
      ((2*𝔞(rawDen q)*𝔞(H))^2*𝔞(zabs (im (rawGaussian q)))-
        2*𝔞(rawDen q)*𝔞(RationalSquareRootBounds.root (plus q) (two*rawDen q) H)*𝔞(RationalSquareRootBounds.root (minus q) (two*rawDen q) H))^2 := by
    ipra_simps
    linear_combination 4*𝔞(rawDen q)^2*𝔞(RationalSquareRootBounds.root (plus q) (two*rawDen q) H)^2*
      𝔞(RationalSquareRootBounds.root (minus q) (two*rawDen q) H)^2*bs1-
      4*𝔞(rawDen q)*𝔞(RationalSquareRootBounds.root (plus q) (two*rawDen q) H)*𝔞(RationalSquareRootBounds.root (minus q) (two*rawDen q) H)*
      (2*𝔞(rawDen q)*𝔞(H))^2*sign-(2*𝔞(rawDen q)*𝔞(H))^4*absY
  ipra_simps
  linear_combination realSquare+isq-𝔞(rawDen q)^2*ap-ai

def imaginaryDefect (q H : PTm n) : PTm n :=
  plusDeficit q H*RationalSquareRootBounds.radicand (minus q) (base q) H+
    (plusRoot q H*plusRoot q H)*minusDeficit q H

theorem imaginary_gap_identity (q H : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    (grid q H*grid q H*zabs (im (rawGaussian q)))*(grid q H*grid q H*zabs (im (rawGaussian q))) ≐
      (two*rawDen q*plusRoot q H*minusRoot q H)*(two*rawDen q*plusRoot q H*minusRoot q H)+
        base q*base q*imaginaryDefect q H := by
  ipra_lc [imaginaryDefect, plusDeficit, minusDeficit, plusRoot, minusRoot, grid, RationalSquareRootBounds.radicand, base] -(2*𝔞(rawDen q)*𝔞(H))^4*natEq (imaginary_product q h)- (2*𝔞(rawDen q))^2*(𝔞(minus q)*(2*𝔞(rawDen q))*𝔞(H)^2)*natEq (RationalSquareRootBounds.root_deficit (Γ := Γ) (plus q) (base q) H)- (2*𝔞(rawDen q))^2*𝔞(RationalSquareRootBounds.root (plus q) (two*rawDen q) H)^2*natEq (RationalSquareRootBounds.root_deficit (Γ := Γ) (minus q) (base q) H)

theorem ad_le_sum (a b : PTm n) : Γ ⊢[PRAAx] le (Probability.Variance.ad a b) (a+b) :=
  Probability.MedianWeighted.ad_le_of
    (le_of_eq_add (d := two*b) (by ipra_ring))
    (le_of_eq_add (d := two*a) (by ipra_ring))

theorem precision_le_grid (q H : PTm n) : Γ ⊢[PRAAx] le H (grid q H) :=
  le_congr (one_mul _) (.eqRefl _) (le_mul_mono (base_positive q) (le_refl H))

theorem imaginary_defect_bound (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (imaginaryDefect q H) ((num 6)*(grid q H*grid q H*grid q H)) := by
  have rmBound : Γ ⊢[PRAAx] le (RationalSquareRootBounds.radicand (minus q) (base q) H) (grid q H*grid q H) :=
    le_congr (by unfold RationalSquareRootBounds.radicand; ipra_ring) (by unfold grid; ipra_ring)
      (mul_le_mul_right (base q*H*H) (minus_bound q h))
  have pBound := RationalSquareRootBounds.deficit_bound (Γ := Γ) (plus q) (base q) H (base_positive q) hH (plus_bound q h)
  have mBound := RationalSquareRootBounds.deficit_bound (Γ := Γ) (minus q) (base q) H (base_positive q) hH (minus_bound q h)
  exact le_congr (.eqRefl _) (by unfold RationalSquareRootBounds.three RationalSquareRootBounds.denominator grid; ipra_ring)
    (add_le_add₂ (le_mul_mono pBound rmBound) (le_mul_mono (sq_le_sq (plus_root_bound q H h)) mBound))

theorem imaginary_gap_bound (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (Probability.Variance.ad (grid q H*grid q H*zabs (im (rawGaussian q))) (two*rawDen q*plusRoot q H*minusRoot q H)*
      Probability.Variance.ad (grid q H*grid q H*zabs (im (rawGaussian q))) (two*rawDen q*plusRoot q H*minusRoot q H))
      ((num 24)*(rawDen q*rawDen q)*(grid q H*grid q H*grid q H)) := by
  have gap := ad_square_gap _ _ (imaginary_root_order q H h)
  have cancelled : Γ ⊢[PRAAx] le
      (Probability.Variance.ad (grid q H*grid q H*zabs (im (rawGaussian q))) (two*rawDen q*plusRoot q H*minusRoot q H)*
        Probability.Variance.ad (grid q H*grid q H*zabs (im (rawGaussian q))) (two*rawDen q*plusRoot q H*minusRoot q H))
      (base q*base q*imaginaryDefect q H) := by
    apply le_of_add_le_add_right (c := (two*rawDen q*plusRoot q H*minusRoot q H)*(two*rawDen q*plusRoot q H*minusRoot q H))
    exact le_congr (.eqRefl _) ((imaginary_gap_identity q H h).eqTrans (add_comm _ _)) gap
  exact le_trans cancelled (le_congr (by ipra_ring) (by unfold base; ipra_ring)
    (mul_le_mul_right (base q*base q) (imaginary_defect_bound q H hH h)))

theorem floor_square_error_cleared (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    le (H*normSq (floorSquareDifference q H))
      ((num 60)*((rawDen q*(grid q H*grid q H))*(rawDen q*(grid q H*grid q H)))) := by
  have adBound := le_trans (ad_le_sum (Γ := Γ) (plusDeficit q H) (minusDeficit q H)) (deficit_bound q H hH h)
  have realBound : Γ ⊢[PRAAx] le
      ((rawDen q*rawDen q)*(Probability.Variance.ad (plusDeficit q H) (minusDeficit q H)*Probability.Variance.ad (plusDeficit q H) (minusDeficit q H)))
      ((num 36)*(rawDen q*rawDen q)*(grid q H*grid q H)) :=
    le_congr (by ipra_ring) (by unfold RationalSquareRootBounds.three; ipra_ring)
      (mul_le_mul_right (rawDen q*rawDen q) (sq_le_sq adBound))
  have total := le_congr (floor_square_difference_norm q H h).eqSymm (.eqRefl _)
    (add_le_add₂ realBound (imaginary_gap_bound q H hH h))
  have Ksq : Γ ⊢[PRAAx] le (grid q H) (grid q H*grid q H) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (grid q H)) (grid_positive q H hH))
  have total' : Γ ⊢[PRAAx] le (normSq (floorSquareDifference q H))
      ((num 60)*(rawDen q*rawDen q)*(grid q H*grid q H*grid q H)) :=
    le_trans total (le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right ((num 36)*(rawDen q*rawDen q)*grid q H) Ksq)
        (le_refl ((num 24)*(rawDen q*rawDen q)*(grid q H*grid q H*grid q H)))))
  exact le_trans (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right H total'))
    (le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right ((num 60)*(rawDen q*rawDen q)*(grid q H*grid q H*grid q H)) (precision_le_grid q H)))

theorem floor_square_error (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (qsub (GaussianRationalHorner.qmul (floorPoint q H) (floorPoint q H)) q)) (fraction (num 60) H) := by
  have hK := grid_positive (Γ := Γ) q H hH
  have hKK := positive_product _ _ hK hK
  have product := GaussianRationalHorner.qmul_represents (Γ := Γ) (floorPoint q H) (floorPoint q H)
    (floorNumerator q H) (floorNumerator q H) (grid q H) (grid q H) hK hK
    (GaussianRationalHorner.ofGaussian_represents _ _ hK) (GaussianRationalHorner.ofGaussian_represents _ _ hK)
  have pRep := GaussianRationalHorner.represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _)
    (mul_comm _ _) (GaussianRationalHorner.represents_rescale _ _ _ (rawDen q) product)
  have qRep := GaussianRationalHorner.represents_rescale _ _ _ (grid q H*grid q H) (raw_represents (Γ := Γ) q)
  have hE := positive_product _ _ (raw_den_positive q) hKK
  have difference := GaussianRationalMetric.qsub_represents _ _ _ _ _ hE pRep qRep
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (positive_product _ _ hE hE) hH
    (GaussianRationalMetric.qnormSq_represents _ _ _ hE difference) (fraction_represents _ _ hH)
  exact floor_square_error_cleared q H hH h

/-- The grid-aligned floors give exact contraction, stronger than a
contraction with an added precision error. -/
theorem half_contraction (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (RationalArithmetic.multiply (fraction two one) (qnormSq (qsub (half q H) GaussianRationalReciprocal.qone)))
      (qnormSq (qsub q GaussianRationalReciprocal.qone)) := by
  have hW := GaussianRationalCircleParametrization.denominator_positive (Γ := Γ)
    (circleL q H) (minusRoot q H) (circleL_positive q H hH)
  have dist := GaussianRationalCircleParametrization.distance_one (Γ := Γ)
    (circleL q H) (minusRoot q H) (negativeBit q) (circleL_positive q H hH) (negative_bit_boolean q)
  have hr := GaussianRationalHorner.scalar_congr dist.eqSymm (ZT.derive rfl) (.eqRefl _)
    (fraction_represents (Γ := Γ) _ _ hW)
  have hi := GaussianRationalHorner.scalar_congr (input_distance q h).eqSymm (ZT.derive rfl) (.eqRefl _)
    (fraction_represents (Γ := Γ) (two*minus q) (rawDen q) (raw_den_positive q))
  have prod := RationalRepresentations.represents_multiply (Γ := Γ)
    (fraction two one) (qnormSq (qsub (half q H) GaussianRationalReciprocal.qone))
    (ZT.ofNat two) (ZT.ofNat (GaussianRationalCircleParametrization.four*minusRoot q H*minusRoot q H)) one (circleDen q H)
    (fraction_represents two one (le_refl one)) hr
  have prod' : Γ ⊢[PRAAx] RationalArithmetic.represents
      (RationalArithmetic.multiply (fraction two one) (qnormSq (qsub (half q H) GaussianRationalReciprocal.qone)))
      (ZT.ofNat (two*(GaussianRationalCircleParametrization.four*minusRoot q H*minusRoot q H))) (circleDen q H) := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _) (h := prod)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hW (raw_den_positive q) prod' hi
  exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two (contraction_cleared q H h))

def projectionNumerator (q H : PTm n) : PTm n := GaussianIntegerCircleProjection.cross
  (plusRoot q H) (minusRoot q H) (negativeBit q) (grid q H)

theorem projection_represents (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    represents (qsub (half q H) (floorPoint q H)) (projectionNumerator q H) (grid q H*circleDen q H) := by
  have hK := grid_positive (Γ := Γ) q H hH
  have hW := GaussianRationalCircleParametrization.denominator_positive (Γ := Γ) (circleL q H) (minusRoot q H) (circleL_positive q H hH)
  have hp := GaussianRationalCircleParametrization.point_represents (Γ := Γ) (circleL q H) (minusRoot q H) (negativeBit q) (circleL_positive q H hH)
  have hr := GaussianRationalHorner.represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _)
    (GaussianRationalHorner.represents_rescale _ _ _ (grid q H) hp)
  have hs := GaussianRationalHorner.represents_rescale _ _ _ (circleDen q H)
    (GaussianRationalHorner.ofGaussian_represents (Γ := Γ) (floorNumerator q H) (grid q H) hK)
  have hd := GaussianRationalMetric.qsub_represents _ _ _ _ _ (positive_product _ _ hK hW) hr hs
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := hd)
  apply GaussianRootAlgebra.equal_of_values
  all_goals
    simp only [projectionNumerator,GaussianIntegerCircleProjection.cross,
      GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianIntegerCircleProjection.re_plane,GaussianIntegerCircleProjection.im_plane,
      floorNumerator,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
      GaussianIntegerCircleProjection.circleNum,GaussianIntegerCircleProjection.circleDen,
      GaussianIntegerCircleProjection.sign,ZT.toZ_sub,ZT.toZ_ofNat,circleNumerator,circleDen,circleL] <;> ipra_simps <;> ring

theorem projection_norm (q H : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    normSq (projectionNumerator q H) ≐ circleDen q H*deficit q H*deficit q H :=
  GaussianIntegerCircleProjection.cross_norm _ _ _ _ _ (negative_bit_boolean q) (roots_deficit q H h).eqSymm

theorem projection_distance (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (half q H) (floorPoint q H) (num 6) H := by
  have hK := grid_positive (Γ := Γ) q H hH
  have hW := GaussianRationalCircleParametrization.denominator_positive (Γ := Γ) (circleL q H) (minusRoot q H) (circleL_positive q H hH)
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (positive_product _ _ hK hW) hH
    (projection_represents q H hH)
  have hHW : Γ ⊢[PRAAx] le (H*H) (circleDen q H) :=
    le_trans (sq_le_sq (precision_le_grid q H))
      (le_trans (sq_le_sq (le_add_right (grid q H) (plusRoot q H))) (le_add_right _ _))
  have budget := mul_le_mul_right (circleDen q H) (le_mul_mono (sq_le_sq (deficit_bound q H hH h)) hHW)
  exact le_congr (by have e := natEq (projection_norm q H h); apply deriveNat; ipra_simps; rw [e]; ring)
    (by unfold RationalSquareRootBounds.three circleDen; ipra_ring) budget

theorem half_bounded (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (half q H) one one := by
  have hW := GaussianRationalCircleParametrization.denominator_positive (Γ := Γ)
    (circleL q H) (minusRoot q H) (circleL_positive q H hH)
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hW (le_refl one)
    (GaussianRationalCircleParametrization.point_represents _ _ _ (circleL_positive q H hH))
  have e := GaussianRationalCircleParametrization.numerator_norm (Γ := Γ)
    (circleL q H) (minusRoot q H) (negativeBit q) (negative_bit_boolean q)
  exact le_congr (by ipra_ring) (by ipra_ring)
    (le_congr e.eqSymm (.eqRefl _) (le_refl _))

theorem half_square_difference (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded
      (GaussianRationalHorner.qmul (half q H) (half q H))
      (GaussianRationalHorner.qmul (floorPoint q H) (floorPoint q H)) (num 12) H := by
  have power := GaussianRationalPowerDifference.unit_disk_power_difference (half q H) (floorPoint q H)
    (num 6) H two hH (half_bounded q H hH) (floor_bounded q H hH h) (projection_distance q H hH h)
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalSyntheticDivision.qsub_congr
      (GaussianRationalPowerAlgebra.power_two (half q H) (half_canonical q H hH))
      (GaussianRationalPowerAlgebra.power_two (floorPoint q H)
        (GaussianRationalHorner.ofGaussian_canonical _ _ (grid_positive q H hH))))
    (by ipra_ring) (.eqRefl _) power

/-- The original unit input alone supplies every coordinate, floor,
projection and square-residual estimate in this bound. -/
theorem half_square_error (q H : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (qnormSq (qsub (GaussianRationalHorner.qmul (half q H) (half q H)) q)) (fraction (num 400) H) := by
  have hHH := positive_product H H hH hH
  have hOrder : Γ ⊢[PRAAx] le H (H*H) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl H) hH)
  have first : Γ ⊢[PRAAx] RationalArgmin.rationalLE
      (qnormSq (qsub (GaussianRationalHorner.qmul (half q H) (half q H))
        (GaussianRationalHorner.qmul (floorPoint q H) (floorPoint q H)))) (fraction ((num 12)*(num 12)) H) :=
    RationalArgmin.transitive (half_square_difference q H hH h)
      (GaussianEuclideanDistanceName.fraction_order _ _ _ _ hHH hH
        (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right ((num 12)*(num 12)) hOrder)))
  have sixty : Γ ⊢[PRAAx] le (num 60 : PTm n) ((num 8)*(num 8)) :=
    le_of_eq_add (d := num 4) (by ipra_ring)
  have second : Γ ⊢[PRAAx] RationalArgmin.rationalLE
      (qnormSq (qsub (GaussianRationalHorner.qmul (floorPoint q H) (floorPoint q H)) q))
      (fraction ((num 8)*(num 8)) H) :=
    RationalArgmin.transitive (floor_square_error q H hH h)
      (GaussianEuclideanDistanceName.fraction_order _ _ _ _ hH hH
        (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right H sixty)))
  have combined := GaussianRationalRelativeTriangle.relative_triangle _ _ (num 12) (num 8) H hH first second
  have chain := GaussianReconstructionRoots.difference_chain (Γ := Γ)
    (GaussianRationalHorner.qmul (half q H) (half q H))
    (GaussianRationalHorner.qmul (floorPoint q H) (floorPoint q H)) q
  have normChain := GaussianRationalProductWitness.qnormSq_congr chain
  exact RationalArgmin.rationalLE_congr normChain
    (RationalNonnegativePowers.fraction_congr (by ipra_ring) (.eqRefl _)) combined

theorem half_square_accuracy_of_budget (q H J : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (h : Γ ⊢[PRAAx] unit q) (hBudget : Γ ⊢[PRAAx] le ((num 400)*pw two J*pw two J) H) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (GaussianRationalHorner.qmul (half q H) (half q H)) q one (pw two J) := by
  have hJ := GaussianBalancedRadiusSyntax.unit_positive (Γ := Γ) J
  change Γ ⊢[PRAAx] RationalArgmin.rationalLE
    (qnormSq (qsub (GaussianRationalHorner.qmul (half q H) (half q H)) q))
    (fraction (one*one) (pw two J*pw two J))
  exact RationalArgmin.transitive (half_square_error q H hH h)
    (GaussianEuclideanDistanceName.fraction_order _ _ _ _ hH (positive_product _ _ hJ hJ)
      (le_congr (by ipra_ring) (by ipra_ring) hBudget))

def precision (J : PTm n) : PTm n := pw two (two*J+num 10)
@[simp] theorem subst_precision {m : ℕ} (σ : Fin n → PTm m) (J : PTm n) :
    Syn.subst σ (precision J) = precision (Syn.subst σ J) := by simp [precision]

theorem two_power_ten : Γ ⊢[PRAAx] pw (two : PTm n) (num 10) ≐ num 1024 := by
  ipra_lc natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 10 ≐ succ (num 9)) (.eqRefl (two : PTm n))).eqTrans (pw_succ two (num 9))))+
    2*natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 9 ≐ succ (num 8)) (.eqRefl (two : PTm n))).eqTrans (pw_succ two (num 8))))+
    4*natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 8 ≐ succ (num 7)) (.eqRefl (two : PTm n))).eqTrans (pw_succ two (num 7))))+
    8*natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 7 ≐ succ (num 6)) (.eqRefl (two : PTm n))).eqTrans (pw_succ two (num 6))))+
    16*natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 6 ≐ succ (num 5)) (.eqRefl (two : PTm n))).eqTrans (pw_succ two (num 5))))+
    32*natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 5 ≐ succ (num 4)) (.eqRefl (two : PTm n))).eqTrans (pw_succ two (num 4))))+
    64*natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 4 ≐ succ (num 3)) (.eqRefl (two : PTm n))).eqTrans (pw_succ two (num 3))))+
    128*natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 3 ≐ succ (num 2)) (.eqRefl (two : PTm n))).eqTrans (pw_succ two (num 2))))+
    256*natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 2 ≐ succ (num 1)) (.eqRefl (two : PTm n))).eqTrans (pw_succ two (num 1))))+
    512*natEq (((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 1 ≐ succ zero) (.eqRefl (two : PTm n))).eqTrans (pw_succ two zero)))+
    1024*natEq (pw_zero (Γ := Γ) (two : PTm n))

theorem precision_factor (J : PTm n) : Γ ⊢[PRAAx]
    precision J ≐ pw two J*pw two J*(num 1024) :=
  (pw_add two (two*J) (num 10)).eqTrans
    (congrMul ((congrAp2 powF (by ipra_ring) (.eqRefl two)).eqTrans (pw_add two J J)) two_power_ten)

theorem precision_positive (J : PTm n) : Γ ⊢[PRAAx] le one (precision J) :=
  GaussianBalancedRadiusSyntax.unit_positive _

theorem precision_budget (J : PTm n) : Γ ⊢[PRAAx] le ((num 400)*pw two J*pw two J) (precision J) := by
  have constant : Γ ⊢[PRAAx] le (num 400 : PTm n) (num 1024) :=
    le_of_eq_add (d := num 624) (by ipra_ring)
  have budget : Γ ⊢[PRAAx] le ((num 400)*(pw two J*pw two J)) ((pw two J*pw two J)*(num 1024)) :=
    le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right (pw two J*pw two J) constant)
  exact le_congr (by ipra_ring) (precision_factor J).eqSymm budget

theorem half_square_accuracy (q J : PTm n) (h : Γ ⊢[PRAAx] unit q) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded
      (GaussianRationalHorner.qmul (half q (precision J)) (half q (precision J))) q one (pw two J) :=
  half_square_accuracy_of_budget q (precision J) J (precision_positive J) h (precision_budget J)

/-! The actual point constructor is PR2. The optional trace contains
that point and its actual circle parameter, signed root and denominator. -/
def halfF : PR 2 := PTm.toPR (half (var 0) (var 1))
def output (q H : PTm n) : PTm n := pairT (half q H)
  (pairT (circleL q H) (pairT (minusRoot q H) (pairT (negativeBit q) (circleDen q H))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (q H : PTm n) : PTm n := ap2 outputF q H

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (output q H) = output (Syn.subst σ q) (Syn.subst σ H) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (q H : PTm n) :
    Syn.subst σ (run q H) = run (Syn.subst σ q) (Syn.subst σ H) := by simp [run]

theorem half_at (q H : PTm n) : Γ ⊢[PRAAx] ap2 halfF q H ≐ half q H := by
  simpa [halfF,ap2] using toPR_eq (Γ := Γ) (half (var 0) (var 1) : PTm 2) ![q,H]

theorem program_at (q H : PTm n) : Γ ⊢[PRAAx] run q H ≐ output q H := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![q,H]

theorem returned_point (q H : PTm n) : Γ ⊢[PRAAx] fstT (run q H) ≐ half q H :=
  (congrFst (program_at q H)).eqTrans (fst_pair _ _)
theorem returned_parameter (q H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run q H)) ≐ circleL q H :=
  (congrFst ((congrSnd (program_at q H)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_root (q H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run q H))) ≐ minusRoot q H :=
  (congrFst ((congrSnd ((congrSnd (program_at q H)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_sign (q H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run q H)))) ≐ negativeBit q :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at q H)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (q H : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run q H)))) ≐ circleDen q H :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at q H)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_accuracy (q H J : PTm n) (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] unit q)
    (hBudget : Γ ⊢[PRAAx] le ((num 400)*pw two J*pw two J) H) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded
      (GaussianRationalHorner.qmul (fstT (run q H)) (fstT (run q H))) q one (pw two J) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianRationalSyntheticDivision.qsub_congr
      (GaussianRationalSyntheticDivision.qmul_congr (returned_point q H).eqSymm (returned_point q H).eqSymm)
      (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (half_square_accuracy_of_budget q H J hH h hBudget)

theorem half_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ unit (half (var 0) (var 1))) :=
  closeUniv 2 (.impI (half_unit _ _ Prf.hyp0))

theorem principal_half_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (unit (var 0) ⟶ le one (var 1) ⟶
      RationalArgmin.rationalLE (fraction zero one) (fstT (half (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.impI (half_real_nonnegative _ _ Prf.hyp0 Prf.hyp1)))

theorem exact_contraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (unit (var 0) ⟶ le one (var 1) ⟶
      RationalArgmin.rationalLE
        (RationalArithmetic.multiply (fraction two one)
          (qnormSq (qsub (half (var 0) (var 1)) GaussianRationalReciprocal.qone)))
        (qnormSq (qsub (var 0) GaussianRationalReciprocal.qone))) :=
  closeUniv 2 (.impI (.impI (half_contraction _ _ Prf.hyp0 Prf.hyp1)))

theorem half_square_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (unit (var 0) ⟶ le one (var 1) ⟶
      RationalArgmin.rationalLE
        (qnormSq (qsub (GaussianRationalHorner.qmul (half (var 0) (var 1)) (half (var 0) (var 1))) (var 0)))
        (fraction (num 400) (var 1))) :=
  closeUniv 2 (.impI (.impI (half_square_error _ _ Prf.hyp0 Prf.hyp1)))

theorem half_square_accuracy_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (unit (var 0) ⟶ le one (var 1) ⟶ le ((num 400)*pw two (var 2)*pw two (var 2)) (var 1) ⟶
      GaussianRationalMetric.distanceBounded
        (GaussianRationalHorner.qmul (half (var 0) (var 1)) (half (var 0) (var 1))) (var 0) one (pw two (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI
    (half_square_accuracy_of_budget _ _ _ Prf.hyp1 Prf.hyp0.wk.wk Prf.hyp0))))

theorem dyadic_half_accuracy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (unit (var 0) ⟶ GaussianRationalMetric.distanceBounded
      (GaussianRationalHorner.qmul (half (var 0) (precision (var 1))) (half (var 0) (precision (var 1))))
      (var 0) one (pw two (var 1))) :=
  closeUniv 2 (.impI (half_square_accuracy _ _ Prf.hyp0))

theorem half_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 halfF (var 0) (var 1) ≐ half (var 0) (var 1)) := closeUniv 2 (half_at _ _)

theorem trace_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

theorem returned_accuracy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (unit (var 0) ⟶ le one (var 1) ⟶ le ((num 400)*pw two (var 2)*pw two (var 2)) (var 1) ⟶
      GaussianRationalMetric.distanceBounded
        (GaussianRationalHorner.qmul (fstT (run (var 0) (var 1))) (fstT (run (var 0) (var 1))))
        (var 0) one (pw two (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI
    (returned_accuracy _ _ _ Prf.hyp1 Prf.hyp0.wk.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalHalfAngle
