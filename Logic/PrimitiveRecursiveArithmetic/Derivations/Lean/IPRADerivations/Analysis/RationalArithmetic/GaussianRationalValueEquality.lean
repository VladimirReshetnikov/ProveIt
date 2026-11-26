import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantPairAlgebra
import IPRADerivations.Analysis.Polynomials.GaussianRationalSyntheticCoefficientValues

/-!
# Exact field-value equality for arbitrary Gaussian rational codes

The predicate compares actual decoded Gaussian numerator cross-products.
It is independent of raw code equality and of the separately proved
canonical recode and zero-subtraction characterizations. All query points,
polynomial lists and Horner prefix indices are numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalValueEquality

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul canonical represents canonical_unique represents_congr positive_product
    horner hornerF horner_zero horner_succ evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qsub_represents qsub_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr qzero_canonical rescale_to)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant
  (recode recode_canonical recode_represents recode_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (scale zeroCode)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_re equal_im equal_of_values equal_refl equal_symm re_scale im_scale re_sub im_sub re_zero im_zero)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def commonDen (q r : PTm n) : PTm n := rawDen q*rawDen r
def leftValue (q r : PTm n) : PTm n := scale (rawDen r) (rawGaussian q)
def rightValue (q r : PTm n) : PTm n := scale (rawDen q) (rawGaussian r)
def valueEqual (q r : PTm n) : Fm PTm n := equal (leftValue q r) (rightValue q r)
@[simp] theorem subst_commonDen {l : ℕ} (σ : Fin n → PTm l) (q r : PTm n) :
    Syn.subst σ (commonDen q r) = commonDen (Syn.subst σ q) (Syn.subst σ r) := by simp [commonDen]
@[simp] theorem subst_leftValue {l : ℕ} (σ : Fin n → PTm l) (q r : PTm n) :
    Syn.subst σ (leftValue q r) = leftValue (Syn.subst σ q) (Syn.subst σ r) := by simp [leftValue]
@[simp] theorem subst_rightValue {l : ℕ} (σ : Fin n → PTm l) (q r : PTm n) :
    Syn.subst σ (rightValue q r) = rightValue (Syn.subst σ q) (Syn.subst σ r) := by simp [rightValue]
@[simp] theorem subst_valueEqual {l : ℕ} (σ : Fin n → PTm l) (q r : PTm n) :
    (valueEqual q r).subst σ = valueEqual (Syn.subst σ q) (Syn.subst σ r) := by simp [valueEqual]

theorem common_den_positive (q r : PTm n) : Γ ⊢[PRAAx] le one (commonDen q r) :=
  positive_product _ _ (raw_den_positive q) (raw_den_positive r)
theorem common_left_represents (q r : PTm n) : Γ ⊢[PRAAx] represents q (leftValue q r) (commonDen q r) :=
  rescale_to _ _ _ _ _ (raw_represents q) (.eqRefl _)
theorem common_right_represents (q r : PTm n) : Γ ⊢[PRAAx] represents r (rightValue q r) (commonDen q r) :=
  rescale_to _ _ _ _ _ (raw_represents r) (mul_comm _ _)

theorem equal_values_of_recode_equal (q r : PTm n) (h : Γ ⊢[PRAAx] recode q ≐ recode r) : Γ ⊢[PRAAx]
    valueEqual q r := GaussianDominantPairAlgebra.represents_cross _ _ _ _ _ (recode_represents q)
      (represents_congr h.eqSymm (equal_refl _) (.eqRefl _) (recode_represents r))

theorem recode_equal_of_equal_values (q r : PTm n) (h : Γ ⊢[PRAAx] valueEqual q r) : Γ ⊢[PRAAx]
    recode q ≐ recode r := by
  have lhs : Γ ⊢[PRAAx] represents (recode q) (leftValue q r) (commonDen q r) :=
    rescale_to _ _ _ _ _ (recode_represents q) (.eqRefl _)
  have rhs : Γ ⊢[PRAAx] represents (recode r) (rightValue q r) (commonDen q r) :=
    rescale_to _ _ _ _ _ (recode_represents r) (mul_comm _ _)
  exact canonical_unique _ _ _ _ (recode_canonical _) (recode_canonical _) (common_den_positive q r)
    lhs (represents_congr (.eqRefl _) (equal_symm h) (.eqRefl _) rhs)

theorem recode_equal_iff (q r : PTm n) : Γ ⊢[PRAAx] Fm.iff (recode q ≐ recode r) (valueEqual q r) :=
  .andI (.impI (equal_values_of_recode_equal q r Prf.hyp0)) (.impI (recode_equal_of_equal_values q r Prf.hyp0))

theorem difference_represents (q r : PTm n) : Γ ⊢[PRAAx]
    represents (qsub q r) (GaussianRootAlgebra.sub (leftValue q r) (rightValue q r)) (commonDen q r) :=
  qsub_represents _ _ _ _ _ (common_den_positive _ _) (common_left_represents _ _) (common_right_represents _ _)

theorem difference_zero_of_equal_values (q r : PTm n) (h : Γ ⊢[PRAAx] valueEqual q r) : Γ ⊢[PRAAx]
    qsub q r ≐ qzero := by
  have value : Γ ⊢[PRAAx] equal (GaussianRootAlgebra.sub (leftValue q r) (rightValue q r)) zeroCode := by
    apply equal_of_values
    · simp only [re_sub,re_zero]
      rw [equal_re h]
      ring
    · simp only [im_sub,im_zero]
      rw [equal_im h]
      ring
  exact canonical_unique _ _ _ _ (qsub_canonical _ _) qzero_canonical (common_den_positive q r)
    (represents_congr (.eqRefl _) value (.eqRefl _) (difference_represents q r)) (GaussianRationalHorner.zero_represents _)

theorem equal_values_of_difference_zero (q r : PTm n) (h : Γ ⊢[PRAAx] qsub q r ≐ qzero) : Γ ⊢[PRAAx]
    valueEqual q r := by
  have rep := represents_congr h (equal_refl _) (.eqRefl _) (difference_represents q r)
  have cleared := GaussianDominantPairAlgebra.represents_cross qzero
    (GaussianRootAlgebra.sub (leftValue q r) (rightValue q r)) zeroCode (commonDen q r) one rep
    (GaussianRationalHorner.zero_represents one)
  apply equal_of_values
  · have e := equal_re cleared
    simp only [re_scale,re_sub,re_zero] at e
    simp only [Q.mk_one,map_one,one_mul,mul_zero] at e
    linear_combination e
  · have e := equal_im cleared
    simp only [im_scale,im_sub,im_zero] at e
    simp only [Q.mk_one,map_one,one_mul,mul_zero] at e
    linear_combination e

theorem difference_zero_iff (q r : PTm n) : Γ ⊢[PRAAx] Fm.iff (qsub q r ≐ qzero) (valueEqual q r) :=
  .andI (.impI (equal_values_of_difference_zero q r Prf.hyp0)) (.impI (difference_zero_of_equal_values q r Prf.hyp0))
theorem recode_eq_iff_difference_zero (q r : PTm n) : Γ ⊢[PRAAx] Fm.iff (recode q ≐ recode r) (qsub q r ≐ qzero) :=
  .andI (.impI (difference_zero_of_equal_values q r (equal_values_of_recode_equal q r Prf.hyp0)))
    (.impI (recode_equal_of_equal_values q r (equal_values_of_difference_zero q r Prf.hyp0)))

theorem value_equal_refl (q : PTm n) : Γ ⊢[PRAAx] valueEqual q q :=
  equal_values_of_recode_equal _ _ (.eqRefl _)
theorem value_equal_symm (q r : PTm n) (h : Γ ⊢[PRAAx] valueEqual q r) : Γ ⊢[PRAAx] valueEqual r q :=
  equal_values_of_recode_equal _ _ (recode_equal_of_equal_values _ _ h).eqSymm
theorem value_equal_trans (q r s : PTm n) (h : Γ ⊢[PRAAx] valueEqual q r) (h' : Γ ⊢[PRAAx] valueEqual r s) : Γ ⊢[PRAAx]
    valueEqual q s := equal_values_of_recode_equal _ _
      ((recode_equal_of_equal_values _ _ h).eqTrans (recode_equal_of_equal_values _ _ h'))
theorem value_equal_of_code {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] valueEqual q r :=
  equal_values_of_recode_equal _ _ (recode_congr h)

theorem qmul_right_recode_equal (a q r : PTm n) (h : Γ ⊢[PRAAx] recode q ≐ recode r) : Γ ⊢[PRAAx]
    qmul a q ≐ qmul a r :=
  (GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) h).eqTrans (GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _))

def queryLaw (C q r k : PTm n) : Fm PTm n := horner C q k ≐ horner C r k
@[simp] theorem subst_queryLaw {l : ℕ} (σ : Fin n → PTm l) (C q r k : PTm n) :
    (queryLaw C q r k).subst σ = queryLaw (Syn.subst σ C) (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ k) := by simp [queryLaw]

/-- Actual equality of normalized Horner outputs is proved by genuine QF
prefix induction. The original coefficient list may contain arbitrary raw codes. -/
theorem horner_query_proper (C q r k : PTm n) (h : Γ ⊢[PRAAx] recode q ≐ recode r) : Γ ⊢[PRAAx]
    horner C q k ≐ horner C r k := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] recode (Syn.shift q) ≐ recode (Syn.shift r) := by
    simpa only [Fm.shift,Fm.subst_eq,GaussianTranslatedNonconstant.subst_recode,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (queryLaw (Syn.shift C) (Syn.shift q) (Syn.shift r) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_queryLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (horner_zero C q).eqTrans (horner_zero C r).eqSymm
    · simp only [subst_queryLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (horner_succ _ _ _).eqTrans
        ((qadd_congr ((qmul_congr (Prf.hyp0 : queryLaw (Syn.shift C) (Syn.shift q) (Syn.shift r) (var 0) :: Γ.map Fm.shift ⊢[PRAAx]
          queryLaw (Syn.shift C) (Syn.shift q) (Syn.shift r) (var 0)) (.eqRefl _)).eqTrans
            (qmul_right_recode_equal _ _ _ hs.wk)) (.eqRefl _)).eqTrans (horner_succ _ _ _).eqSymm)
  have law : Γ ⊢[PRAAx] queryLaw C q r k := by
    simpa only [subst_queryLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact law

theorem horner_value_proper (C q r k : PTm n) (h : Γ ⊢[PRAAx] valueEqual q r) : Γ ⊢[PRAAx]
    horner C q k ≐ horner C r k := horner_query_proper _ _ _ _ (recode_equal_of_equal_values _ _ h)
theorem evaluation_query_proper (C q r : PTm n) (h : Γ ⊢[PRAAx] recode q ≐ recode r) : Γ ⊢[PRAAx]
    evaluate C q ≐ evaluate C r := horner_query_proper C q r (length C) h
theorem evaluation_value_proper (C q r : PTm n) (h : Γ ⊢[PRAAx] valueEqual q r) : Γ ⊢[PRAAx]
    evaluate C q ≐ evaluate C r := evaluation_query_proper _ _ _ (recode_equal_of_equal_values _ _ h)
theorem evaluation_zero_transport (C q r : PTm n) (h : Γ ⊢[PRAAx] valueEqual q r)
    (hZero : Γ ⊢[PRAAx] evaluate C q ≐ qzero) : Γ ⊢[PRAAx] evaluate C r ≐ qzero :=
  (evaluation_value_proper _ _ _ h).eqSymm.eqTrans hZero

/-! The actual PR2 output retains both canonical value keys and the literal
normalized difference; its checker accepts exactly native field equality. -/
def output (q r : PTm n) : PTm n := pairT (recode q) (pairT (recode r) (qsub q r))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (q r : PTm n) : PTm n := ap2 outputF q r
def checkerF : PR 2 := PTm.toPR (eqb (recode (var 0)) (recode (var 1)))
def check (q r : PTm n) : PTm n := ap2 checkerF q r
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (q r : PTm n) :
    Syn.subst σ (output q r) = output (Syn.subst σ q) (Syn.subst σ r) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (q r : PTm n) :
    Syn.subst σ (run q r) = run (Syn.subst σ q) (Syn.subst σ r) := by simp [run]
@[simp] theorem subst_check {l : ℕ} (σ : Fin n → PTm l) (q r : PTm n) :
    Syn.subst σ (check q r) = check (Syn.subst σ q) (Syn.subst σ r) := by simp [check]
theorem program_at (q r : PTm n) : Γ ⊢[PRAAx] run q r ≐ output q r := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![q,r]
theorem checker_at (q r : PTm n) : Γ ⊢[PRAAx] check q r ≐ eqb (recode q) (recode r) := by
  simpa [check,checkerF,ap2] using toPR_eq (Γ := Γ) (eqb (recode (var 0)) (recode (var 1)) : PTm 2) ![q,r]
theorem checker_reflection (q r : PTm n) : Γ ⊢[PRAAx] Fm.iff (check q r ≐ one) (valueEqual q r) :=
  .andI (.impI (equal_values_of_recode_equal _ _
    (Foundations.BoundedReflection.eq_of_eqb ((checker_at q r).wk.eqSymm.eqTrans Prf.hyp0))))
    (.impI ((checker_at q r).wk.eqTrans (eqb_of_eq (recode_equal_of_equal_values _ _ Prf.hyp0))))
theorem returned_left (q r : PTm n) : Γ ⊢[PRAAx] fstT (run q r) ≐ recode q :=
  (congrFst (program_at _ _)).eqTrans (fst_pair _ _)
theorem returned_right (q r : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run q r)) ≐ recode r :=
  (congrFst ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_difference (q r : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run q r)) ≐ qsub q r :=
  (congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_difference_zero (q r : PTm n) (h : Γ ⊢[PRAAx] valueEqual q r) : Γ ⊢[PRAAx]
    sndT (sndT (run q r)) ≐ qzero := (returned_difference _ _).eqTrans (difference_zero_of_equal_values _ _ h)

/-! All original raw values, coefficient lists and prefix counts are bound
inside these genuine ordinary-Prf statements. -/
theorem canonical_keys_equal_iff_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (recode (var 0) ≐ recode (var 1)) (valueEqual (var 0) (var 1))) :=
  closeUniv 2 (recode_equal_iff _ _)
theorem actual_difference_zero_iff_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (qsub (var 0) (var 1) ≐ qzero) (valueEqual (var 0) (var 1))) :=
  closeUniv 2 (difference_zero_iff _ _)
theorem canonical_keys_equal_iff_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (recode (var 0) ≐ recode (var 1)) (qsub (var 0) (var 1) ≐ qzero)) :=
  closeUniv 2 (recode_eq_iff_difference_zero _ _)
theorem actual_horner_value_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (valueEqual (var 1) (var 2) ⟶ horner (var 0) (var 1) (var 3) ≐ horner (var 0) (var 2) (var 3)) :=
  closeUniv 4 (.impI (horner_value_proper _ _ _ _ Prf.hyp0))
theorem actual_polynomial_value_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (valueEqual (var 1) (var 2) ⟶ evaluate (var 0) (var 1) ≐ evaluate (var 0) (var 2)) :=
  closeUniv 3 (.impI (evaluation_value_proper _ _ _ Prf.hyp0))
theorem actual_polynomial_zero_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (valueEqual (var 1) (var 2) ⟶ evaluate (var 0) (var 1) ≐ qzero ⟶ evaluate (var 0) (var 2) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (evaluation_zero_transport _ _ _ Prf.hyp1 Prf.hyp0)))
theorem value_equality_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem native_value_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (check (var 0) (var 1) ≐ one) (valueEqual (var 0) (var 1))) := closeUniv 2 (checker_reflection _ _)
theorem returned_equal_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (valueEqual (var 0) (var 1) ⟶ sndT (sndT (run (var 0) (var 1))) ≐ qzero) :=
  closeUniv 2 (.impI (returned_difference_zero _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalValueEquality
