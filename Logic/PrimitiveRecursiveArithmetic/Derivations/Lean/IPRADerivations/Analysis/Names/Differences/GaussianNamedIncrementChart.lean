import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedIncrementDifferenceQuotient
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianL1
import IPRADerivations.Core.CommonLemmas

/-!
# Common rational chart for a named Gaussian base and increment

The two original observations give a single positive denominator.
Their recoded values and literal sum are unchanged by the common
rescaling. A late observation of an apart increment has a nonzero
native numerator, and its rational upper bound controls the cleared
step size used in finite first-order estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianNamedIncrementChart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add scale normSq normSq_scale bounded_add)
open GaussianFastValueCut (recode exponent recode_bound_iff)
open GaussianGammaEncodingRescaling (fraction_rescale fraction_denominator_congr)
open GaussianL1 (norm1 norm1_square_le_two_normSq)
open GaussianNameArithmetic (addF addData)
open GaussianNamedDifferenceQuotient (separated)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical positive_product canonical_unique
  qadd qadd_canonical qadd_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive)
open GaussianRationalMetric (bounded bounded_iff distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRootApproximationWitness (pointBounds)
open LeanProofs.IPRA.Common (le_of_sq_le mul_cancel_le)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (q r : PTm n) : PTm n := rawDen q*rawDen r
def baseNumerator (q r : PTm n) : PTm n := scale (rawDen r) (rawGaussian q)
def stepNumerator (q r : PTm n) : PTm n := scale (rawDen q) (rawGaussian r)

def certificate (q r : PTm n) : Fm PTm n :=
  separated (stepNumerator q r) (denominator q r) ⋏
    ((ofGaussian (baseNumerator q r) (denominator q r) ≐ recode q) ⋏
     ((ofGaussian (stepNumerator q r) (denominator q r) ≐ recode r) ⋏
      (ofGaussian (add (baseNumerator q r) (stepNumerator q r)) (denominator q r) ≐ qadd (recode q) (recode r))))

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (q r : PTm n) :
    Syn.subst σ (denominator q r) = denominator (Syn.subst σ q) (Syn.subst σ r) := by simp [denominator]

@[simp] theorem subst_baseNumerator {m : ℕ} (σ : Fin n → PTm m) (q r : PTm n) :
    Syn.subst σ (baseNumerator q r) = baseNumerator (Syn.subst σ q) (Syn.subst σ r) := by simp [baseNumerator]

@[simp] theorem subst_stepNumerator {m : ℕ} (σ : Fin n → PTm m) (q r : PTm n) :
    Syn.subst σ (stepNumerator q r) = stepNumerator (Syn.subst σ q) (Syn.subst σ r) := by simp [stepNumerator]

@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (q r : PTm n) :
    (certificate q r).subst σ = certificate (Syn.subst σ q) (Syn.subst σ r) := by simp [certificate,separated,one]

theorem denominator_positive (q r : PTm n) : Γ ⊢[PRAAx] le one (denominator q r) :=
  positive_product _ _ (raw_den_positive q) (raw_den_positive r)

theorem base_fraction (q r : PTm n) : Γ ⊢[PRAAx] ofGaussian (baseNumerator q r) (denominator q r) ≐ recode q := by
  have e := fraction_denominator_congr (Γ := Γ) (baseNumerator q r) (denominator q r) (rawDen r*rawDen q) (mul_comm _ _)
  exact e.eqTrans (fraction_rescale (rawGaussian q) (rawDen q) (rawDen r) (raw_den_positive q) (raw_den_positive r))

theorem step_fraction (q r : PTm n) : Γ ⊢[PRAAx] ofGaussian (stepNumerator q r) (denominator q r) ≐ recode r :=
  fraction_rescale (rawGaussian r) (rawDen r) (rawDen q) (raw_den_positive r) (raw_den_positive q)

theorem shared_denominator_sum (z h D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qadd (ofGaussian z D) (ofGaussian h D) ≐ ofGaussian (add z h) D :=
  canonical_unique _ _ (add z h) D (qadd_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (qadd_represents _ _ z h D hD (ofGaussian_represents z D hD) (ofGaussian_represents h D hD))
    (ofGaussian_represents (add z h) D hD)

theorem sum_fraction (q r : PTm n) :
    Γ ⊢[PRAAx] ofGaussian (add (baseNumerator q r) (stepNumerator q r)) (denominator q r) ≐ qadd (recode q) (recode r) :=
  (shared_denominator_sum _ _ _ (denominator_positive q r)).eqSymm.eqTrans
    (qadd_congr (base_fraction q r) (step_fraction q r))

theorem sum_fraction_raw (q r : PTm n) :
    Γ ⊢[PRAAx] ofGaussian (add (baseNumerator q r) (stepNumerator q r)) (denominator q r) ≐ qadd q r := by
  have e (v : PTm n) : Γ ⊢[PRAAx] recode v ≐ GaussianTranslatedNonconstant.recode v :=
    canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical v) (GaussianTranslatedNonconstant.recode_canonical v)
      (raw_den_positive v) (GaussianFastValueCut.recode_represents v) (GaussianTranslatedNonconstant.recode_represents v)
  exact (sum_fraction q r).eqTrans ((qadd_congr (e q) (e r)).eqTrans
    ((GaussianRationalSyntheticCoefficientValues.qadd_recode_left q (GaussianTranslatedNonconstant.recode r)).eqTrans
      (GaussianRationalSyntheticCoefficientValues.qadd_recode_right q r)))

theorem step_separated (q r : PTm n) (hr : Γ ⊢[PRAAx] le one (normSq (rawGaussian r))) :
    Γ ⊢[PRAAx] separated (stepNumerator q r) (denominator q r) := by
  have h := raw_den_positive (Γ := Γ) q
  have norm := positive_product _ _ (positive_product _ _ h h) hr
  exact .andI (denominator_positive q r)
    (le_congr (.eqRefl _) (normSq_scale (rawDen q) (rawGaussian r)).eqSymm norm)

theorem late_chart (F K : PR 2) (p x a y t : PTm n) (hs : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a y) :
    Γ ⊢[PRAAx] certificate (ap2 F p x) (GaussianNameReciprocal.tail K a y t) := by
  let q := ap2 F p x
  let r := GaussianNameReciprocal.tail K a y t
  have h : Γ ⊢[PRAAx] le one (normSq (rawGaussian r)) :=
    (GaussianNamedIncrementDifferenceQuotient.late_native_separated K a y t hs).andE₂
  exact .andI (step_separated q r h) (.andI (base_fraction q r) (.andI (step_fraction q r) (sum_fraction q r)))

theorem late_step_value (K : PR 2) (q a y t : PTm n) :
    let r := GaussianNameReciprocal.tail K a y t
    Γ ⊢[PRAAx] distanceBounded (ofGaussian (stepNumerator q r) (denominator q r))
      (ap2 K (t+GaussianNameReciprocal.anchor a) y) zero one :=
  distance_congr (step_fraction q _).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedIncrementDifferenceQuotient.late_native_value K a y t)

theorem actual_sum_at (F K : PR 2) (p x y : PTm n) :
    let j := exponent two p
    let q := ap2 F j x
    let r := ap2 K j y
    Γ ⊢[PRAAx] ofGaussian (add (baseNumerator q r) (stepNumerator q r)) (denominator q r) ≐
      ap2 (addF F K) p (addData x y) := by
  let j := exponent two p
  let q := ap2 F j x
  let r := ap2 K j y
  have eq : Γ ⊢[PRAAx] ap2 (addF F K) p (addData x y) ≐ qadd q r :=
    (GaussianNameArithmetic.add_at F K x y p).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qadd_canonical q r))
  exact (sum_fraction_raw q r).eqTrans eq.eqSymm

theorem late_actual_sum_at (F K : PR 2) (p x a y t : PTm n)
    (ht : Γ ⊢[PRAAx] t+GaussianNameReciprocal.anchor a ≐ exponent two p) :
    let q := ap2 F (t+GaussianNameReciprocal.anchor a) x
    let r := GaussianNameReciprocal.tail K a y t
    Γ ⊢[PRAAx] ofGaussian (add (baseNumerator q r) (stepNumerator q r)) (denominator q r) ≐
      ap2 (addF F K) p (addData x y) := by
  let j := t+GaussianNameReciprocal.anchor a
  let k := exponent two p
  let q := ap2 F j x
  let r := ap2 K j y
  let u := ap2 F k x
  let v := ap2 K k y
  have e : Γ ⊢[PRAAx] ofGaussian (add (baseNumerator q r) (stepNumerator q r)) (denominator q r) ≐
      ofGaussian (add (baseNumerator u v) (stepNumerator u v)) (denominator u v) := by
    have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (ofGaussian (add (baseNumerator (var 0) (var 1)) (stepNumerator (var 0) (var 1)))
        (denominator (var 0) (var 1)) : PTm 2)
      (σ := ![q,r]) (σ' := ![u,v]) (fun i => by
        fin_cases i
        · exact congrAp2 F ht (.eqRefl x)
        · exact congrAp2 K ht (.eqRefl y))
    simpa using h
  exact e.eqTrans (actual_sum_at F K p x y)

private theorem cleared_bound (q z D A M : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hM : Γ ⊢[PRAAx] le one M)
    (he : Γ ⊢[PRAAx] ofGaussian z D ≐ recode q) (h : Γ ⊢[PRAAx] bounded q A M) :
    Γ ⊢[PRAAx] le ((M*M)*normSq z) ((A*A)*(D*D)) := by
  have e := (recode_bound_iff q A M hM).iffMpr h
  exact (bounded_iff _ _ _ _ _ hD hM (ofGaussian_represents z D hD)).iffMp
    (bound_congr he.eqSymm (.eqRefl _) (.eqRefl _) e)

theorem base_disk (q r R : PTm n) (h : Γ ⊢[PRAAx] bounded q R one) :
    Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (baseNumerator q r) (R*denominator q r) := by
  exact le_congr (by ipra_ring) (by ipra_ring)
    (cleared_bound q _ _ R one (denominator_positive q r) (le_refl one) (base_fraction q r) h)

theorem step_disk (q r S : PTm n) (h : Γ ⊢[PRAAx] bounded r S one) :
    Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (stepNumerator q r) (S*denominator q r) := by
  exact le_congr (by ipra_ring) (by ipra_ring)
    (cleared_bound r _ _ S one (denominator_positive q r) (le_refl one) (step_fraction q r) h)

theorem base_source (F : PR 2) (p x r R : PTm n) (h : Γ ⊢[PRAAx] pointBounds F R x) :
    Γ ⊢[PRAAx] le one (denominator (ap2 F p x) r) ⋏
      ComplexLogarithmRemainder.bounded (baseNumerator (ap2 F p x) r) (R*denominator (ap2 F p x) r) :=
  .andI (denominator_positive _ _) (base_disk (ap2 F p x) r R (GaussianRootApproximationWitness.point_at F R x p h))

theorem sum_disk (q r R S : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) (hr : Γ ⊢[PRAAx] bounded r S one) :
    Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (add (baseNumerator q r) (stepNumerator q r)) ((R+S)*denominator q r) := by
  have b := bounded_add (base_disk q r R hq) (step_disk q r S hr)
  exact le_congr (.eqRefl _) (by ipra_ring) b

theorem sum_disk_of_raw_sum (q r R : PTm n) (h : Γ ⊢[PRAAx] bounded (qadd q r) R one) :
    Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (add (baseNumerator q r) (stepNumerator q r)) (R*denominator q r) := by
  have e := (sum_fraction_raw (Γ := Γ) q r).eqTrans (GaussianExponentialReference.recode_fixed _ (qadd_canonical q r)).eqSymm
  exact le_congr (by ipra_ring) (by ipra_ring)
    (cleared_bound (qadd q r) _ _ R one (denominator_positive q r) (le_refl one) e h)

theorem step_norm1_bound (q r A M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] bounded r A M) :
    Γ ⊢[PRAAx] le (norm1 (stepNumerator q r)*M) (two*A*denominator q r) := by
  let h := stepNumerator q r
  let D := denominator q r
  let X := A*A*(D*D)
  have e := cleared_bound r h D A M (denominator_positive q r) hM (step_fraction q r) hr
  have l : Γ ⊢[PRAAx] le ((norm1 h*M)*(norm1 h*M)) (two*((M*M)*normSq h)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (M*M) (norm1_square_le_two_normSq h))
  have rr : Γ ⊢[PRAAx] le (two*X) ((two*A*D)*(two*A*D)) :=
    le_of_eq_add (d := two*X) (by unfold X; ipra_ring)
  apply le_of_sq_le
  exact le_trans l (le_trans (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right two e)) rr)

theorem step_small (q r A M C : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] bounded r A M)
    (hC : Γ ⊢[PRAAx] le (two*C*A) M) :
    Γ ⊢[PRAAx] le (C*norm1 (stepNumerator q r)) (denominator q r) := by
  let h := stepNumerator q r
  let D := denominator q r
  have a : Γ ⊢[PRAAx] le (M*(C*norm1 h)) ((two*C*A)*D) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right C (step_norm1_bound q r A M hM hr))
  exact mul_cancel_le hM (le_trans a (mul_le_mul_right D hC))

theorem actual_named_gaussian_increment_chart_closed (F K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (GaussianNameReciprocal.input K (var 2) (var 3) ⟶
        certificate (ap2 F (var 0) (var 1)) (GaussianNameReciprocal.tail K (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (late_chart F K _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedIncrementChart
