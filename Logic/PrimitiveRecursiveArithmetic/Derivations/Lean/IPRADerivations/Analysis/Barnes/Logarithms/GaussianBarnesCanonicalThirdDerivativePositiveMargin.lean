import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalThirdDerivativeStep
import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalThirdLogarithmRows

/-!
# Positive-axis charts for the next Barnes logarithmic derivative

For A/B and C/B with A,B,C≥1 and common real margin 1/K, every
original Barnes base at both points has modulus at least 1/K.
This admits the exact second-to-third row expansion uniformly in k.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdDerivativePositiveMargin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Common (add_le_add mul_le_mul)
open ComplexLogarithmRemainder (add code)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalThirdDerivativeStep (errorNumerator errorDenominator increment linear)
open GaussianBarnesCanonicalThirdLogarithmRows (base_at center derivative_at row shiftedNumerator)
open GaussianDominantPairAlgebra (radiusPoint radius_represents radius_numerator_norm)
open GaussianRationalHorner (canonical_unique positive_product qadd_canonical represents_congr ofGaussian qmul)
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRootAlgebra (equal equal_of_values equal_refl add_equal)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "second" => GaussianBarnesCanonicalSecondDerivativeRow.value

def step (A C : PTm n) : PTm n := code (ZT.ofNat C-ZT.ofNat A) (ZT.ofNat zero)

def source (A C B H K : PTm n) : Fm PTm n :=
  le one B ⋏ (le one A ⋏ (le one C ⋏ (le one K ⋏
    (le B (K*A) ⋏ (le B (K*C) ⋏ ComplexLogarithmRemainder.bounded (step A C) H)))))

@[simp] theorem subst_step {m : ℕ} (σ : Fin n → PTm m) (A C : PTm n) :
    Syn.subst σ (step A C) = step (Syn.subst σ A) (Syn.subst σ C) := by simp [step]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (A C B H K : PTm n) :
    (source A C B H K).subst σ = source (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B)
      (Syn.subst σ H) (Syn.subst σ K) := by simp [source,one]

theorem shifted_center (A C B : PTm n) : Γ ⊢[PRAAx] equal (add (center A B) (step A C)) (center C B) := by
  apply equal_of_values
  · simp only [center,step,GaussianRootAlgebra.re_add,ComplexLogarithmRemainder.eval_re_code,ZT.toZ_sub,ZT.toZ_ofNat]
    ring
  · simp only [center,step,GaussianRootAlgebra.im_add,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring

theorem base_congr {z w : PTm n} (B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hk : Γ ⊢[PRAAx] le one k) (h : Γ ⊢[PRAAx] equal z w) :
    Γ ⊢[PRAAx] base z B k ≐ base w B k := by
  let D := B*k
  let W := GaussianGammaEulerHeadLower.translated w B k
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hB hk
  have trans : Γ ⊢[PRAAx] equal (GaussianGammaEulerHeadLower.translated z B k) W :=
    add_equal h (equal_refl _)
  exact canonical_unique _ _ W D (qadd_canonical _ _) (qadd_canonical _ _) hD
    (represents_congr (.eqRefl _) trans (.eqRefl _) (GaussianBarnesCanonicalBase.base_represents _ _ _ hB hk))
    (GaussianBarnesCanonicalBase.base_represents _ _ _ hB hk)

theorem base_lower (A B i K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hK : Γ ⊢[PRAAx] le one K) (hA : Γ ⊢[PRAAx] le B (K*A)) :
    Γ ⊢[PRAAx] lower (base (center A B) B (succ i)) one K := by
  let D := B*succ i
  let a := shiftedNumerator A B i
  have hD := positive_product B (succ i) hB (zero_lt_succ i)
  have compare : Γ ⊢[PRAAx] le D (K*a) := by
    have grow : Γ ⊢[PRAAx] le (i*B) (K*(i*B)) :=
      le_congr (one_mul _) (.eqRefl _) (mul_le_mul hK (le_refl (i*B)))
    exact le_congr (by dsimp only [D]; ipra_ring) (by dsimp only [a,shiftedNumerator]; ipra_ring) (add_le_add hA grow)
  have clear : Γ ⊢[PRAAx] le (one*one*(D*D)) (K*K*ComplexLogarithmRemainder.normSq
      (GaussianDominantPairAlgebra.radiusNumerator a)) :=
    le_congr (by ipra_ring) ((by ipra_ring : Γ ⊢[PRAAx] (K*a)*(K*a) ≐ (K*K)*(a*a)).eqTrans
      (congrMul (.eqRefl _) (radius_numerator_norm a).eqSymm)) (mul_le_mul compare compare)
  exact lower_congr (base_at A B i hB).eqSymm (.eqRefl _) (.eqRefl _)
    (lower_from_representation (radiusPoint a D) _ D one K hD hK (radius_represents a D hD) clear)

theorem row_source (A C B H K i : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalThirdDerivativeStep.source (center A B) (step A C) B (succ i) H K := by
  have hB := h.andE₁
  have hk : Γ ⊢[PRAAx] le one (succ i) := zero_lt_succ i
  have hK := h.andE₂.andE₂.andE₂.andE₁
  have hz := base_lower A B i K hB hK h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hw := base_lower C B i K hB hK h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have e := base_congr B (succ i) hB hk (shifted_center A C B)
  exact .andI hB (.andI hk (.andI hK (.andI hz (.andI
    (lower_congr e.eqSymm (.eqRefl _) (.eqRefl _) hw) h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))))

theorem increment_at (A C B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] increment (center A B) (step A C) B (succ i) ≐
      qsub (second (center C B) B (succ i)) (second (center A B) B (succ i)) := by
  have e := GaussianNameReciprocal.reciprocal_congr (base_congr B (succ i) hB (zero_lt_succ i) (shifted_center A C B))
  exact qsub_congr (qmul_congr (.eqRefl _) (qsub_congr (.eqRefl _) (qmul_congr e e))) (.eqRefl _)

theorem row_error (A C B H K i : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (second (center C B) B (succ i)) (second (center A B) B (succ i)))
      (qmul (ofGaussian (step A C) B) (row A B i))
      (errorNumerator H K) (errorDenominator B (succ i)) :=
  GaussianRationalDistanceOrder.distance_congr (increment_at A C B i h.andE₁)
    (qmul_congr (.eqRefl _) (derivative_at A B i h.andE₂.andE₁ h.andE₁)) (.eqRefl _) (.eqRefl _)
    (GaussianBarnesCanonicalThirdDerivativeStep.quadratic_bound _ _ _ _ _ _ (row_source A C B H K i h))

theorem actual_Barnes_positive_axis_second_row_third_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let A := var 0
       let C := var 1
       let B := var 2
       let H := var 3
       let K := var 4
       let i := var 5
       source A C B H K ⟶ distanceBounded
         (qsub (second (center C B) B (succ i)) (second (center A B) B (succ i)))
         (qmul (ofGaussian (step A C) B) (row A B i))
         (errorNumerator H K) (errorDenominator B (succ i))) :=
  closeUniv 6 (.impI (row_error _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdDerivativePositiveMargin
