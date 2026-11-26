import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalReciprocal
import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName

/-!
# Actual rational unit-circle parametrization with a Boolean sign

The computed point has numerator (L^2-V^2, 2LV-4bLV) and denominator
L^2+V^2. A genuine Boolean flag b selects either sign of the imaginary
coordinate; the zero flag selects the nonnegative branch. The exact
Pythagorean identity proves unit squared norm, and the actual normalized
difference from one has squared norm 4V^2/(L^2+V^2). No unit, distance,
representation or canonical-output assertion is an input premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalCircleParametrization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (code re im normSq normSq_eval scale oneCode)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (ofGaussian positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (qone)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def four : PTm n := two*two
def realNumerator (L V : PTm n) : ZT n := ZT.ofNat (L*L)-ZT.ofNat (V*V)
def imagNumerator (L V b : PTm n) : ZT n := ZT.ofNat (two*L*V)-ZT.ofNat (b*four*L*V)
def numerator (L V b : PTm n) : PTm n := code (realNumerator L V) (imagNumerator L V b)
def denominator (L V : PTm n) : PTm n := L*L+V*V
def point (L V b : PTm n) : PTm n := ofGaussian (numerator L V b) (denominator L V)
def bit (b : PTm n) : Fm PTm n := b ≐ zero ⋎ b ≐ one

@[simp] theorem subst_four {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (four : PTm n) = (four : PTm m) := by simp [four]
@[simp] theorem subst_realNumerator {m : ℕ} (σ : Fin n → PTm m) (L V : PTm n) :
    (realNumerator L V).subst σ = realNumerator (Syn.subst σ L) (Syn.subst σ V) := by simp [realNumerator]
@[simp] theorem subst_imagNumerator {m : ℕ} (σ : Fin n → PTm m) (L V b : PTm n) :
    (imagNumerator L V b).subst σ = imagNumerator (Syn.subst σ L) (Syn.subst σ V) (Syn.subst σ b) := by simp [imagNumerator]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (L V b : PTm n) :
    Syn.subst σ (numerator L V b) = numerator (Syn.subst σ L) (Syn.subst σ V) (Syn.subst σ b) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (L V : PTm n) :
    Syn.subst σ (denominator L V) = denominator (Syn.subst σ L) (Syn.subst σ V) := by simp [denominator]
@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (L V b : PTm n) :
    Syn.subst σ (point L V b) = point (Syn.subst σ L) (Syn.subst σ V) (Syn.subst σ b) := by simp [point]
@[simp] theorem subst_bit {m : ℕ} (σ : Fin n → PTm m) (b : PTm n) :
    (bit b).subst σ = bit (Syn.subst σ b) := by simp [bit]

theorem re_numerator (L V b : PTm n) : ZT.toZ Γ (re (numerator L V b)) = ZT.toZ Γ (realNumerator L V) :=
  ComplexLogarithmRemainder.eval_re_code _ _
theorem im_numerator (L V b : PTm n) : ZT.toZ Γ (im (numerator L V b)) = ZT.toZ Γ (imagNumerator L V b) :=
  ComplexLogarithmRemainder.eval_im_code _ _

theorem denominator_positive (L V : PTm n) (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx] le one (denominator L V) :=
  le_trans (positive_product L L hL hL) (le_add_right _ _)

theorem point_represents (L V b : PTm n) (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents (point L V b) (numerator L V b) (denominator L V) :=
  GaussianRationalHorner.ofGaussian_represents _ _ (denominator_positive L V hL)

theorem point_canonical (L V b : PTm n) (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (point L V b) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (denominator_positive L V hL)

theorem real_represents (L V b : PTm n) (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (point L V b)) (realNumerator L V) (denominator L V) := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := Prf.andE₁ (point_represents L V b hL))
  exact ZT.derive (re_numerator L V b)

theorem imag_represents (L V b : PTm n) (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (sndT (point L V b)) (imagNumerator L V b) (denominator L V) := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := Prf.andE₂ (point_represents L V b hL))
  exact ZT.derive (im_numerator L V b)

/-- Pythagoras for the actual two signed numerator programs. The
Boolean domain is the only sign hypothesis; L and V may both be zero. -/
theorem numerator_norm (L V b : PTm n) (hb : Γ ⊢[PRAAx] bit b) : Γ ⊢[PRAAx]
    normSq (numerator L V b) ≐ denominator L V*denominator L V := by
  refine .orE hb ?_ ?_
  · have e := natEq (Prf.hyp0 : (b ≐ zero)::Γ ⊢[PRAAx] b ≐ zero)
    apply deriveNat
    rw [normSq_eval,re_numerator,im_numerator]
    unfold realNumerator imagNumerator denominator four
    simp only [ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    rw [e]
    ring
  · have e := natEq (Prf.hyp0 : (b ≐ one)::Γ ⊢[PRAAx] b ≐ one)
    apply deriveNat
    rw [normSq_eval,re_numerator,im_numerator]
    unfold realNumerator imagNumerator denominator four
    simp only [ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    rw [e]
    ring

theorem unit_norm (L V b : PTm n) (hL : Γ ⊢[PRAAx] le one L) (hb : Γ ⊢[PRAAx] bit b) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq (point L V b) ≐ fraction one one := by
  have hD := denominator_positive L V hL
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalMetric.qnormSq_canonical _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (GaussianRationalMetric.qnormSq_represents _ _ _ hD (point_represents L V b hL))
    (fraction_represents one one (le_refl one)) (positive_product _ _ hD hD) (le_refl one)
  apply ZT.derive
  have e := natEq (numerator_norm (Γ := Γ) L V b hb)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  rw [e]
  ring

def differenceNumerator (L V b : PTm n) : PTm n :=
  GaussianRootAlgebra.sub (numerator L V b) (scale (denominator L V) oneCode)

@[simp] theorem subst_differenceNumerator {m : ℕ} (σ : Fin n → PTm m) (L V b : PTm n) :
    Syn.subst σ (differenceNumerator L V b) = differenceNumerator (Syn.subst σ L) (Syn.subst σ V) (Syn.subst σ b) := by simp [differenceNumerator]

theorem difference_numerator_norm (L V b : PTm n) (hb : Γ ⊢[PRAAx] bit b) : Γ ⊢[PRAAx]
    normSq (differenceNumerator L V b) ≐ four*V*V*denominator L V := by
  have e := natEq (numerator_norm (Γ := Γ) L V b hb)
  rw [normSq_eval,re_numerator,im_numerator] at e
  apply deriveNat
  rw [normSq_eval]
  unfold differenceNumerator
  simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,
    GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  rw [re_numerator,im_numerator]
  unfold realNumerator imagNumerator denominator four at e ⊢
  simp only [ZT.toZ_sub,ZT.toZ_ofNat] at e ⊢
  ipra_simps
  linear_combination e

theorem distance_one (L V b : PTm n) (hL : Γ ⊢[PRAAx] le one L) (hb : Γ ⊢[PRAAx] bit b) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq (GaussianRationalMetric.qsub (point L V b) qone) ≐ fraction (four*V*V) (denominator L V) := by
  have hD := denominator_positive L V hL
  have difference := GaussianRationalMetric.qsub_represents _ _ _ _ _ hD (point_represents L V b hL)
    (GaussianRationalReciprocal.qone_represents_scaled _)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalMetric.qnormSq_canonical _)
    (RationalNormalForm.normalize_well_formed _ _ hD)
    (GaussianRationalMetric.qnormSq_represents _ _ _ hD difference)
    (fraction_represents _ _ hD) (positive_product _ _ hD hD) hD
  apply ZT.derive
  have e := natEq (difference_numerator_norm (Γ := Γ) L V b hb)
  unfold differenceNumerator at e
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  rw [e]
  ring

theorem real_nonnegative_order (L V b : PTm n) (hL : Γ ⊢[PRAAx] le one L)
    (hVL : Γ ⊢[PRAAx] le V L) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fraction zero one) (fstT (point L V b)) := by
  have squared := le_mul_mono hVL hVL
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _
    (fraction_represents zero one (le_refl one)) (real_represents L V b hL)
    (le_refl one) (denominator_positive L V hL)
  apply zle_of_toZ (monus (L*L) (V*V))
  have e := natEq (eq_add_of_le squared)
  simp only [realNumerator,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -e

/-! The point constructor itself is PR3. A separate literal output
carries that point and its actually computed numerator and denominator. -/
def pointF : PR 3 := PTm.toPR (point (var 0) (var 1) (var 2))
def output (L V b : PTm n) : PTm n := pairT (point L V b) (pairT (numerator L V b) (denominator L V))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (L V b : PTm n) : PTm n := ap3 outputF L V b

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (L V b : PTm n) :
    Syn.subst σ (output L V b) = output (Syn.subst σ L) (Syn.subst σ V) (Syn.subst σ b) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (L V b : PTm n) :
    Syn.subst σ (run L V b) = run (Syn.subst σ L) (Syn.subst σ V) (Syn.subst σ b) := by simp [run]

theorem point_program (L V b : PTm n) : Γ ⊢[PRAAx] ap3 pointF L V b ≐ point L V b := by
  simpa [pointF,ap3] using toPR_eq (Γ := Γ) (point (var 0) (var 1) (var 2) : PTm 3) ![L,V,b]
theorem program_at (L V b : PTm n) : Γ ⊢[PRAAx] run L V b ≐ output L V b := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![L,V,b]

theorem returned_point (L V b : PTm n) : Γ ⊢[PRAAx] fstT (run L V b) ≐ point L V b :=
  (congrFst (program_at L V b)).eqTrans (fst_pair _ _)
theorem returned_numerator (L V b : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run L V b)) ≐ numerator L V b :=
  (congrFst ((congrSnd (program_at L V b)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (L V b : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run L V b)) ≐ denominator L V :=
  (congrSnd ((congrSnd (program_at L V b)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem rational_circle_pythagorean_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (bit (var 2) ⟶ normSq (numerator (var 0) (var 1) (var 2)) ≐ denominator (var 0) (var 1)*denominator (var 0) (var 1)) :=
  closeUniv 3 (.impI (numerator_norm _ _ _ Prf.hyp0))

theorem rational_circle_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ bit (var 2) ⟶
      (GaussianRationalHorner.canonical (point (var 0) (var 1) (var 2)) ⋏
        GaussianRationalMetric.qnormSq (point (var 0) (var 1) (var 2)) ≐ fraction one one)) :=
  closeUniv 3 (.impI (.impI (.andI (point_canonical _ _ _ Prf.hyp1) (unit_norm _ _ _ Prf.hyp1 Prf.hyp0))))

theorem rational_circle_distance_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ bit (var 2) ⟶
      GaussianRationalMetric.qnormSq (GaussianRationalMetric.qsub (point (var 0) (var 1) (var 2)) qone) ≐
        fraction (four*var 1*var 1) (denominator (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (distance_one _ _ _ Prf.hyp1 Prf.hyp0)))

theorem rational_circle_real_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ RationalArithmetic.represents (fstT (point (var 0) (var 1) (var 2)))
      (realNumerator (var 0) (var 1)) (denominator (var 0) (var 1))) :=
  closeUniv 3 (.impI (real_represents _ _ _ Prf.hyp0))

theorem rational_circle_nonnegative_real_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le (var 1) (var 0) ⟶
      RationalArgmin.rationalLE (fraction zero one) (fstT (point (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (real_nonnegative_order _ _ _ Prf.hyp1 Prf.hyp0)))

theorem rational_circle_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 pointF (var 0) (var 1) (var 2) ≐ point (var 0) (var 1) (var 2) ⋏
      (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2) ⋏
        (fstT (run (var 0) (var 1) (var 2)) ≐ point (var 0) (var 1) (var 2) ⋏
          (fstT (sndT (run (var 0) (var 1) (var 2))) ≐ numerator (var 0) (var 1) (var 2) ⋏
            sndT (sndT (run (var 0) (var 1) (var 2))) ≐ denominator (var 0) (var 1))))) :=
  closeUniv 3 (.andI (point_program _ _ _) (.andI (program_at _ _ _)
    (.andI (returned_point _ _ _) (.andI (returned_numerator _ _ _) (returned_denominator _ _ _)))))

end LeanProofs.IPRA.Analysis.GaussianRationalCircleParametrization
