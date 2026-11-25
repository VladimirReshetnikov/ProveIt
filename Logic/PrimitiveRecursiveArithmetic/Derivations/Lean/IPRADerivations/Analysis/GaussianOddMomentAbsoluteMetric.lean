import IPRADerivations.Analysis.GaussianGammaRealValues
import IPRADerivations.Analysis.GaussianPositiveRealArithmetic

/-!
# Absolute values of the original real Gaussian observations

The actual rational absolute-value operation projects to the real axis
and takes the scalar absolute value. It preserves the original
Euclidean error budget, fixes nonnegative canonical real points, and
takes identical values on a point and its reflection.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianOddMomentAbsoluteMetric

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_neg zabs_sq zabs_tri)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of)
open RationalGaussianEmbedding (embed native)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianRationalL1 (scalarAbs scalar_abs_represents rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalHorner (represents canonical canonical_unique positive_product represents_congr)
open GaussianPositiveRealArithmetic (positive)
open GaussianRationalMetric (distanceBounded qnegative)
open ComplexLogarithmRemainder (re normSq scale)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def absolute (q : PTm n) : PTm n := embed (scalarAbs (fstT q))

@[simp] theorem subst_absolute {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (absolute q) = absolute (Syn.subst σ q) := by simp [absolute]

theorem absolute_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) :
    Γ ⊢[PRAAx] absolute q ≐ absolute r := by
  simpa only [subst_absolute,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (absolute (var 0) : PTm 1) (σ := ![q]) (σ' := ![r])
      (fun i => by fin_cases i; exact h)

theorem absolute_represents (q a E : PTm n) (h : Γ ⊢[PRAAx] represents q a E) :
    Γ ⊢[PRAAx] represents (absolute q) (native (ZT.ofNat (zabs (re a)))) E :=
  RationalGaussianEmbedding.embed_from_representation _ _ _ (scalar_abs_represents _ _ _ h.andE₁)

theorem absolute_canonical (q : PTm n) : Γ ⊢[PRAAx] canonical (absolute q) :=
  RationalGaussianEmbedding.embed_canonical _

theorem absolute_positive (q : PTm n) : Γ ⊢[PRAAx] positive (absolute q) :=
  GaussianPositiveRealArithmetic.positive_from_representation _ _ _ (absolute_canonical _) (raw_den_positive _)
    (absolute_represents q _ _ (raw_represents q))

private theorem integer_abs_distance (u v : ZT n) : Γ ⊢[PRAAx]
    le (zabs (ZT.ofNat (zabs u) - ZT.ofNat (zabs v))) (zabs (u-v)) := by
  have a : Γ ⊢[PRAAx] le (zabs u) (zabs v+zabs (u-v)) :=
    zabs_tri (by rw [ZT.toZ_sub]; ring)
  have b : Γ ⊢[PRAAx] le (zabs v) (zabs u+zabs (-(u-v))) :=
    zabs_tri (by rw [ZT.toZ_neg,ZT.toZ_sub]; ring)
  have h := ad_le_of a (le_congr (.eqRefl _) (congrAdd (.eqRefl _) (zabs_neg (u-v))) b)
  exact le_congr (zabs_congr (u := ZT.ofNat (zabs u) - ZT.ofNat (zabs v))
    (v := ⟨zabs u,zabs v⟩) (by rw [ZT.toZ_sub,ZT.toZ_ofNat,ZT.toZ_ofNat]; rfl)).eqSymm (.eqRefl _) h

private theorem native_difference_norm (u v : ZT n) : Γ ⊢[PRAAx]
    normSq (GaussianRootAlgebra.sub (native u) (native v)) ≐ zabs (u-v)*zabs (u-v) := by
  apply deriveNat
  rw [ComplexLogarithmRemainder.normSq_eval,zabs_sq]
  simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,native,
    ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat,ZT.toZ_sub]
  ipra_simps
  ring

private theorem absolute_difference_norm_le (a b : PTm n) : Γ ⊢[PRAAx]
    le (normSq (GaussianRootAlgebra.sub
      (native (ZT.ofNat (zabs (re a)))) (native (ZT.ofNat (zabs (re b))))))
      (normSq (GaussianRootAlgebra.sub a b)) := by
  have hab := integer_abs_distance (Γ := Γ) (re a) (re b)
  exact le_trans
    (le_congr (native_difference_norm _ _).eqSymm (native_difference_norm (re a) (re b)).eqSymm
      (AnalyticNumberTheory.PhiLower.le_mul_mono hab hab))
    (GaussianGammaRealValues.real_difference_norm_le a b)

/-- The original Euclidean radius controls the scalar absolute-value
difference even for codes with nonzero imaginary components. -/
theorem absolute_distance (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx]
    distanceBounded (absolute q) (absolute r) A B := by
  let a := scale (rawDen r) (rawGaussian q)
  let b := scale (rawDen q) (rawGaussian r)
  let E := rawDen q*rawDen r
  have hE := positive_product (Γ := Γ) _ _ (raw_den_positive q) (raw_den_positive r)
  have hq : Γ ⊢[PRAAx] represents q a E :=
    GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _ (raw_represents q) (.eqRefl _)
  have hr : Γ ⊢[PRAAx] represents r b E :=
    GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _ (raw_represents r) (mul_comm _ _)
  have old := (GaussianRationalMetric.bounded_difference_iff q r a b E A B hE hB hq hr).iffMp h
  exact (GaussianRationalMetric.bounded_difference_iff _ _ _ _ E A B hE hB
    (absolute_represents q a E hq) (absolute_represents r b E hr)).iffMpr
      (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) (absolute_difference_norm_le a b)) old)

theorem absolute_of_positive (q : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (hp : Γ ⊢[PRAAx] positive q) : Γ ⊢[PRAAx] absolute q ≐ q := by
  let x := fstT q
  let D := denominatorOf x
  let m := GaussianPositiveRealArithmetic.numerator x
  have pos := RationalArgmin.denominator_positive (Γ := Γ) x
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents x (ZT.ofNat m) D :=
    GaussianPositiveRealArithmetic.natural_representation x hp.andE₂
  have hAbs : Γ ⊢[PRAAx] represents (absolute q) (native (ZT.ofNat m)) D := by
    apply RationalGaussianEmbedding.embed_from_representation
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
      (scalar_abs_represents x _ D rep)
    apply ZT.derive
    simpa only [ZT.toZ_ofNat] using natEq (GaussianL1.abs_ofNat (Γ := Γ) m)
  exact (canonical_unique _ _ _ D (absolute_canonical q) (RationalGaussianEmbedding.embed_canonical x)
    pos hAbs (RationalGaussianEmbedding.embed_from_representation x _ D rep)).eqTrans
      (RationalGaussianEmbedding.canonical_axis_roundtrip q hc hp.andE₁)

theorem absolute_negative (q : PTm n) : Γ ⊢[PRAAx] absolute (qnegative q) ≐ absolute q := by
  let a := rawGaussian q
  let D := rawDen q
  apply canonical_unique _ _ (native (ZT.ofNat (zabs (re a)))) D (absolute_canonical _) (absolute_canonical _)
    (raw_den_positive q) ?_ (absolute_represents q a D (raw_represents q))
  have h := absolute_represents (Γ := Γ) (qnegative q) (ComplexLogarithmRemainder.neg a) D
    (GaussianRationalMetric.qnegative_represents q a D (raw_represents q))
  refine represents_congr (.eqRefl _) ?_ (.eqRefl _) h
  apply GaussianRootAlgebra.equal_of_values
  · simp only [native,ComplexLogarithmRemainder.eval_re_code,ZT.toZ_ofNat]
    have e := (zabs_congr (Γ := Γ) (u := re (ComplexLogarithmRemainder.neg a)) (v := -(re a))
      (by simp only [GaussianRootAlgebra.re_neg,ZT.toZ_neg])).eqTrans (zabs_neg (re a))
    exact natEq e
  · simp only [native,ComplexLogarithmRemainder.eval_im_code]

theorem actual_rational_absolute_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (absolute (var 0)) (absolute (var 1)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (absolute_distance _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_rational_absolute_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (positive (absolute (var 0)) ⋏ (canonical (var 0) ⟶ positive (var 0) ⟶ absolute (var 0) ≐ var 0)) :=
  closeUniv 1 (.andI (absolute_positive _) (.impI (.impI (absolute_of_positive _ Prf.hyp1 Prf.hyp0))))

theorem actual_rational_absolute_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (absolute (qnegative (var 0)) ≐ absolute (var 0)) :=
  closeUniv 1 (absolute_negative _)

end LeanProofs.IPRA.Analysis.GaussianOddMomentAbsoluteMetric
