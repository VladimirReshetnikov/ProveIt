import IPRADerivations.Analysis.RationalArithmetic.RationalAlgebra
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalValueEquality
import IPRADerivations.Core.LinearCombination

/-!
# The original rational codes inside the Gaussian rational codes

The real-axis embedding normalizes the original signed numerator and positive
decoded denominator. Equality reflection compares field values, not arbitrary
raw codes. Its arithmetic identities are literal equalities of canonical
outputs. This scalar bridge does not yet transport lists, matrices or norms.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalEq denominator_positive)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_re equal_im equal_refl equal_symm equal_of_values re_add im_add
    re_mul im_mul re_neg im_neg re_scale im_scale re_zero im_zero)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im scale zeroCode)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qzero_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def scalarZero : PTm n := normalize (ZT.ofNat zero) one
def scalarOne : PTm n := normalize (ZT.ofNat one) one
def native (a : ZT n) : PTm n := ComplexLogarithmRemainder.code a (ZT.ofNat zero)
def embed (q : PTm n) : PTm n := pairT (RationalArithmetic.recode q) scalarZero
def axis (q : PTm n) : Fm PTm n := rationalEq (sndT q) scalarZero

@[simp] theorem subst_scalarZero {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (scalarZero : PTm n) = scalarZero := by simp [scalarZero]
@[simp] theorem subst_scalarOne {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (scalarOne : PTm n) = scalarOne := by simp [scalarOne]
@[simp] theorem subst_native {l : ℕ} (σ : Fin n → PTm l) (a : ZT n) :
    Syn.subst σ (native a) = native (ZT.subst σ a) := by simp [native]
@[simp] theorem subst_embed {l : ℕ} (σ : Fin n → PTm l) (q : PTm n) :
    Syn.subst σ (embed q) = embed (Syn.subst σ q) := by simp [embed,RationalArithmetic.recode]
@[simp] theorem subst_axis {l : ℕ} (σ : Fin n → PTm l) (q : PTm n) :
    (axis q).subst σ = axis (Syn.subst σ q) := by simp [axis]

theorem scalar_recode_represents (q : PTm n) (a : ZT n) (A : PTm n)
    (hq : Γ ⊢[PRAAx] RationalArithmetic.represents q a A) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (RationalArithmetic.recode q) a A := by
  apply RationalNormalForm.positive_integer_cancel (denominatorOf q) _ _ (denominator_positive q)
  ipra_lc [RationalArithmetic.represents] 𝔞(denominatorOf (RationalArithmetic.recode q))*ZT.toZ_eq hq+
    𝔞(A)*ZT.toZ_eq (RationalArithmetic.recode_value (Γ := Γ) q)

theorem scalar_zero_represents (A : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents scalarZero (ZT.ofNat zero) A := by
  ipra_lc [zero_mul, mul_one, RationalArithmetic.represents, scalarZero] 𝔞(A)*ZT.toZ_eq (normalize_preserves_value (Γ := Γ) (ZT.ofNat zero) one (le_refl one))

theorem embed_canonical (q : PTm n) : Γ ⊢[PRAAx] canonical (embed q) :=
  canonical_pair _ _ (RationalArithmetic.recode_guard q)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))

theorem embed_from_representation (q : PTm n) (a : ZT n) (A : PTm n)
    (hq : Γ ⊢[PRAAx] RationalArithmetic.represents q a A) :
    Γ ⊢[PRAAx] represents (embed q) (native a) A := by
  refine .andI (scalar_congr (fst_pair _ _).eqSymm ?_ (.eqRefl _)
      (scalar_recode_represents q a A hq))
    (scalar_congr (snd_pair _ _).eqSymm ?_ (.eqRefl _) (scalar_zero_represents A))
  all_goals apply ZT.derive; simp [native,ComplexLogarithmRemainder.eval_re_code,
    ComplexLogarithmRemainder.eval_im_code]

theorem embed_represents (q : PTm n) : Γ ⊢[PRAAx]
    represents (embed q) (native (numeratorOf q)) (denominatorOf q) :=
  embed_from_representation _ _ _ (RationalRepresentations.represents_self q)

theorem embed_zero : Γ ⊢[PRAAx] embed (scalarZero : PTm n) ≐ qzero :=
  canonical_unique _ _ _ _ (embed_canonical _) qzero_canonical (le_refl one)
    (embed_from_representation _ _ _ (scalar_zero_represents one)) (zero_represents one)

theorem embed_one : Γ ⊢[PRAAx] embed (scalarOne : PTm n) ≐ GaussianRationalReciprocal.qone :=
  canonical_unique _ _ _ _ (embed_canonical _) GaussianRationalSyntheticDivision.qone_canonical (le_refl one)
    (embed_from_representation _ _ _ (normalize_preserves_value _ _ (le_refl one)))
    (ofGaussian_represents _ _ (le_refl one))

theorem embed_recode (q : PTm n) : Γ ⊢[PRAAx]
    embed (RationalArithmetic.recode q) ≐ embed q :=
  congrPairT (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.recode_guard q)) (.eqRefl _)

theorem embed_add (a b : PTm n) : Γ ⊢[PRAAx]
    embed (RationalArithmetic.add a b) ≐ qadd (embed a) (embed b) := by
  let A := denominatorOf a
  let B := denominatorOf b
  have ha := represents_rescale (Γ := Γ) _ _ _ B (embed_represents a)
  have hb := represents_rescale (Γ := Γ) _ _ _ A (embed_represents b)
  have hb' := represents_congr (.eqRefl _) (equal_refl _) (mul_comm B A) hb
  have rhs := qadd_represents _ _ _ _ (A*B)
    (positive_product _ _ (denominator_positive a) (denominator_positive b)) ha hb'
  apply canonical_unique _ _ _ _ (embed_canonical _) (qadd_canonical _ _)
    (positive_product _ _ (denominator_positive a) (denominator_positive b))
    (embed_from_representation _ _ _ (RationalArithmetic.add_value a b))
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) rhs
  apply equal_of_values
  all_goals simp [native,A,B,RationalArithmetic.addNumerator,re_add,im_add,re_scale,im_scale,
    ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
    ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] <;> ring

theorem embed_multiply (a b : PTm n) : Γ ⊢[PRAAx]
    embed (RationalArithmetic.multiply a b) ≐ qmul (embed a) (embed b) := by
  have rhs := qmul_represents _ _ _ _ _ _ (denominator_positive a) (denominator_positive b)
    (embed_represents (Γ := Γ) a) (embed_represents b)
  apply canonical_unique _ _ _ _ (embed_canonical _) (qmul_canonical _ _)
    (positive_product _ _ (denominator_positive a) (denominator_positive b))
    (embed_from_representation _ _ _ (RationalArithmetic.multiply_value a b))
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) rhs
  apply equal_of_values
  all_goals simp [native,re_mul,im_mul,ComplexLogarithmRemainder.eval_re_code,
    ComplexLogarithmRemainder.eval_im_code,ZT.toZ_mul,ZT.toZ_ofNat]

theorem embed_negative (a : PTm n) : Γ ⊢[PRAAx]
    embed (RationalArithmetic.negative a) ≐ qnegative (embed a) := by
  apply canonical_unique _ _ _ _ (embed_canonical _) (qnegative_canonical _) (denominator_positive a)
    (embed_from_representation _ _ _ (RationalArithmetic.negative_value a))
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) (qnegative_represents _ _ _ (embed_represents a))
  apply equal_of_values
  all_goals simp [native,re_neg,im_neg,ComplexLogarithmRemainder.eval_re_code,
    ComplexLogarithmRemainder.eval_im_code,ZT.toZ_neg,ZT.toZ_ofNat]

theorem rational_cross (a b : PTm n) (h : Γ ⊢[PRAAx] rationalEq a b) :
    Γ ⊢[PRAAx] ZT.eq (numeratorOf a*ZT.ofNat (denominatorOf b))
      (numeratorOf b*ZT.ofNat (denominatorOf a)) := by
  apply ZT.derive
  have e := natEq h
  simp only [RationalArgmin.left,Q.mk_add,Q.mk_mul,map_add,map_mul] at e
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  linear_combination e

theorem scalar_recode_equal (a b : PTm n) (h : Γ ⊢[PRAAx] rationalEq a b) :
    Γ ⊢[PRAAx] RationalArithmetic.recode a ≐ RationalArithmetic.recode b :=
  RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.recode_guard _) (RationalArithmetic.recode_guard _)
    (RationalArithmetic.recode_value _) (RationalArithmetic.recode_value _)
    (denominator_positive _) (denominator_positive _) (rational_cross a b h)

theorem rational_equal_of_scalar_recode (a b : PTm n)
    (h : Γ ⊢[PRAAx] RationalArithmetic.recode a ≐ RationalArithmetic.recode b) :
    Γ ⊢[PRAAx] rationalEq a b :=
  RationalArithmetic.value_equality _ _ (GaussianDominantPairAlgebra.scalar_representation_cross
    _ _ _ _ _ (RationalArithmetic.recode_value a)
      (scalar_congr h.eqSymm (.eqRefl _) (.eqRefl _) (RationalArithmetic.recode_value b)))

theorem embed_equal (a b : PTm n) (h : Γ ⊢[PRAAx] rationalEq a b) :
    Γ ⊢[PRAAx] embed a ≐ embed b := congrPairT (scalar_recode_equal a b h) (.eqRefl _)

theorem rational_equal_of_embed (a b : PTm n) (h : Γ ⊢[PRAAx] embed a ≐ embed b) :
    Γ ⊢[PRAAx] rationalEq a b := rational_equal_of_scalar_recode a b
      ((fst_pair _ _).eqSymm.eqTrans ((congrFst h).eqTrans (fst_pair _ _)))

theorem eq_iff (a b : PTm n) : Γ ⊢[PRAAx] Fm.iff (rationalEq a b)
    (GaussianRationalValueEquality.valueEqual (embed a) (embed b)) := by
  refine .andI (.impI (GaussianRationalValueEquality.value_equal_of_code (embed_equal a b Prf.hyp0)))
    (.impI ?_)
  have e := GaussianRationalValueEquality.recode_equal_of_equal_values
    (Γ := GaussianRationalValueEquality.valueEqual (embed a) (embed b) :: Γ) (embed a) (embed b) Prf.hyp0
  exact rational_equal_of_embed a b
    ((GaussianTranslatedNonconstant.recode_eq _ (embed_canonical _)).eqSymm.eqTrans
      (e.eqTrans (GaussianTranslatedNonconstant.recode_eq _ (embed_canonical _))))

theorem scalar_recode_zero : Γ ⊢[PRAAx] RationalArithmetic.recode (scalarZero : PTm n) ≐ scalarZero :=
  RationalNormalForm.normalize_fixed_point _ (RationalNormalForm.normalize_well_formed _ _ (le_refl one))

theorem recode_pair (q : PTm n) : Γ ⊢[PRAAx] GaussianTranslatedNonconstant.recode q ≐
    pairT (RationalArithmetic.recode (fstT q)) (RationalArithmetic.recode (sndT q)) := by
  have h := GaussianRationalL1.raw_represents (Γ := Γ) q
  apply canonical_unique _ _ _ _ (GaussianTranslatedNonconstant.recode_canonical q)
    (canonical_pair _ _ (RationalArithmetic.recode_guard _) (RationalArithmetic.recode_guard _))
    (GaussianRationalL1.raw_den_positive q) (GaussianTranslatedNonconstant.recode_represents q)
  exact .andI (scalar_congr (fst_pair _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (scalar_recode_represents _ _ _ (Prf.andE₁ h)))
    (scalar_congr (snd_pair _ _).eqSymm (.eqRefl _) (.eqRefl _)
      (scalar_recode_represents _ _ _ (Prf.andE₂ h)))

theorem axis_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) (hq : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] axis r := RationalArgmin.rationalEq_congr (congrSnd h) (.eqRefl _) hq

theorem embed_axis (a : PTm n) : Γ ⊢[PRAAx] axis (embed a) :=
  RationalArgmin.rationalEq_congr (snd_pair _ _).eqSymm (.eqRefl _) (.eqRefl _)

theorem axis_roundtrip (q : PTm n) (hq : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] GaussianTranslatedNonconstant.recode q ≐ embed (fstT q) :=
  (recode_pair q).eqTrans (congrPairT (.eqRefl _)
    ((scalar_recode_equal _ _ hq).eqTrans scalar_recode_zero))

theorem axis_of_recode_embed (q a : PTm n)
    (h : Γ ⊢[PRAAx] GaussianTranslatedNonconstant.recode q ≐ embed a) :
    Γ ⊢[PRAAx] axis q := by
  have e := ((congrSnd (recode_pair q)).eqTrans (snd_pair _ _)).eqSymm.eqTrans
    ((congrSnd h).eqTrans (snd_pair _ _))
  exact rational_equal_of_scalar_recode _ _ (e.eqTrans scalar_recode_zero.eqSymm)

theorem axis_iff_roundtrip (q : PTm n) : Γ ⊢[PRAAx] Fm.iff (axis q)
    (GaussianTranslatedNonconstant.recode q ≐ embed (fstT q)) :=
  .andI (.impI (axis_roundtrip q Prf.hyp0)) (.impI (axis_of_recode_embed q _ Prf.hyp0))

theorem axis_add_representation (q r : PTm n) (hq : Γ ⊢[PRAAx] axis q) (hr : Γ ⊢[PRAAx] axis r) :
    Γ ⊢[PRAAx] qadd q r ≐ embed (RationalArithmetic.add (fstT q) (fstT r)) :=
  (GaussianRationalSyntheticCoefficientValues.qadd_recode_left q r).eqSymm.eqTrans
    ((GaussianRationalSyntheticCoefficientValues.qadd_recode_right _ r).eqSymm.eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (axis_roundtrip q hq) (axis_roundtrip r hr)).eqTrans
        (embed_add _ _).eqSymm))

theorem axis_multiply_representation (q r : PTm n) (hq : Γ ⊢[PRAAx] axis q) (hr : Γ ⊢[PRAAx] axis r) :
    Γ ⊢[PRAAx] qmul q r ≐ embed (RationalArithmetic.multiply (fstT q) (fstT r)) :=
  (GaussianRationalSyntheticCoefficientValues.qmul_recode_left q r).eqSymm.eqTrans
    ((GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ r).eqSymm.eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (axis_roundtrip q hq) (axis_roundtrip r hr)).eqTrans
        (embed_multiply _ _).eqSymm))

theorem axis_add (q r : PTm n) (hq : Γ ⊢[PRAAx] axis q) (hr : Γ ⊢[PRAAx] axis r) :
    Γ ⊢[PRAAx] axis (qadd q r) :=
  axis_congr (axis_add_representation q r hq hr).eqSymm (embed_axis _)

theorem axis_multiply (q r : PTm n) (hq : Γ ⊢[PRAAx] axis q) (hr : Γ ⊢[PRAAx] axis r) :
    Γ ⊢[PRAAx] axis (qmul q r) :=
  axis_congr (axis_multiply_representation q r hq hr).eqSymm (embed_axis _)

theorem scalar_negative_recode (q : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.negative (RationalArithmetic.recode q) ≐ RationalArithmetic.negative q :=
  RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.negative_guard _) (RationalArithmetic.negative_guard _)
    (RationalRepresentations.represents_negative _ _ _ (RationalArithmetic.recode_value q))
    (RationalArithmetic.negative_value q) (denominator_positive q) (denominator_positive q) (.eqRefl _)

theorem negative_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) :
    Γ ⊢[PRAAx] qnegative q ≐ qnegative r :=
  congrPairT (RationalAlgebra.negative_congr (congrFst h))
    (RationalAlgebra.negative_congr (congrSnd h))

theorem negative_recode (q : PTm n) : Γ ⊢[PRAAx]
    qnegative (GaussianTranslatedNonconstant.recode q) ≐ qnegative q :=
  congrPairT
    ((RationalAlgebra.negative_congr ((congrFst (recode_pair q)).eqTrans (fst_pair _ _))).eqTrans
      (scalar_negative_recode _))
    ((RationalAlgebra.negative_congr ((congrSnd (recode_pair q)).eqTrans (snd_pair _ _))).eqTrans
      (scalar_negative_recode _))

theorem axis_negative_representation (q : PTm n) (hq : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] qnegative q ≐ embed (RationalArithmetic.negative (fstT q)) :=
  (negative_recode q).eqSymm.eqTrans
    ((negative_congr (axis_roundtrip q hq)).eqTrans (embed_negative _).eqSymm)

theorem axis_negative (q : PTm n) (hq : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] axis (qnegative q) :=
  axis_congr (axis_negative_representation q hq).eqSymm (embed_axis _)

theorem axis_zero : Γ ⊢[PRAAx] axis (qzero : PTm n) := axis_congr embed_zero (embed_axis _)
theorem axis_one : Γ ⊢[PRAAx] axis (GaussianRationalReciprocal.qone : PTm n) :=
  axis_congr embed_one (embed_axis _)

theorem embed_eq_iff (a b : PTm n) : Γ ⊢[PRAAx] Fm.iff (embed a ≐ embed b) (rationalEq a b) :=
  .andI (.impI (rational_equal_of_embed a b Prf.hyp0)) (.impI (embed_equal a b Prf.hyp0))

theorem zero_iff (a : PTm n) : Γ ⊢[PRAAx] Fm.iff (embed a ≐ qzero) (rationalEq a scalarZero) :=
  .andI (.impI (rational_equal_of_embed a scalarZero (Prf.hyp0.eqTrans embed_zero.eqSymm)))
    (.impI ((embed_equal a scalarZero Prf.hyp0).eqTrans embed_zero))

theorem canonical_axis_roundtrip (q : PTm n) (hc : Γ ⊢[PRAAx] canonical q) (hq : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] embed (fstT q) ≐ q :=
  (axis_roundtrip q hq).eqSymm.eqTrans (GaussianTranslatedNonconstant.recode_eq q hc)

def embedF : PR 1 := PTm.toPR (embed (var 0))
theorem embed_at (q : PTm n) : Γ ⊢[PRAAx] ap1 embedF q ≐ embed q := by
  simpa only [embedF,ap1,subst_embed,Syn.subst_var,Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (embed (var 0) : PTm 1) ![q]
theorem embed_real_part (q : PTm n) : Γ ⊢[PRAAx] fstT (ap1 embedF q) ≐ RationalArithmetic.recode q :=
  (congrFst (embed_at q)).eqTrans (fst_pair _ _)
theorem embed_imaginary_part (q : PTm n) : Γ ⊢[PRAAx] sndT (ap1 embedF q) ≐ scalarZero :=
  (congrSnd (embed_at q)).eqTrans (snd_pair _ _)
theorem program_canonical (q : PTm n) : Γ ⊢[PRAAx] canonical (ap1 embedF q) :=
  canonical_congr (embed_at q) (embed_canonical q)
theorem program_axis (q : PTm n) : Γ ⊢[PRAAx] axis (ap1 embedF q) :=
  axis_congr (embed_at q).eqSymm (embed_axis q)

theorem original_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (represents (embed (var 0)) (native (numeratorOf (var 0))) (denominatorOf (var 0))) :=
  closeUniv 1 (embed_represents _)
theorem embedding_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (RationalArithmetic.add (var 0) (var 1)) ≐ qadd (embed (var 0)) (embed (var 1)) ⋏
      (embed (RationalArithmetic.multiply (var 0) (var 1)) ≐ qmul (embed (var 0)) (embed (var 1)) ⋏
        embed (RationalArithmetic.negative (var 0)) ≐ qnegative (embed (var 0)))) :=
  closeUniv 2 (.andI (embed_add _ _) (.andI (embed_multiply _ _) (embed_negative _)))
theorem embedding_constants_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (embed scalarZero ≐ qzero ⋏ embed scalarOne ≐ GaussianRationalReciprocal.qone) :=
  .andI embed_zero embed_one
theorem equality_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (rationalEq (var 0) (var 1))
      (GaussianRationalValueEquality.valueEqual (embed (var 0)) (embed (var 1)))) :=
  closeUniv 2 (eq_iff _ _)
theorem real_axis_roundtrip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (Fm.iff (axis (var 0)) (GaussianTranslatedNonconstant.recode (var 0) ≐ embed (fstT (var 0)))) :=
  closeUniv 1 (axis_iff_roundtrip _)
theorem real_axis_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (axis (var 0) ⟶ axis (var 1) ⟶
      (axis (qadd (var 0) (var 1)) ⋏ (axis (qmul (var 0) (var 1)) ⋏ axis (qnegative (var 0))))) :=
  closeUniv 2 (.impI (.impI (.andI (axis_add _ _ Prf.hyp1 Prf.hyp0)
    (.andI (axis_multiply _ _ Prf.hyp1 Prf.hyp0) (axis_negative _ Prf.hyp1)))))
theorem original_zero_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (Fm.iff (embed (var 0) ≐ qzero) (rationalEq (var 0) scalarZero)) := closeUniv 1 (zero_iff _)
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 embedF (var 0) ≐ embed (var 0) ⋏
      (canonical (ap1 embedF (var 0)) ⋏ axis (ap1 embedF (var 0)))) :=
  closeUniv 1 (.andI (embed_at _) (.andI (program_canonical _) (program_axis _)))

end LeanProofs.IPRA.Analysis.RationalGaussianEmbedding
