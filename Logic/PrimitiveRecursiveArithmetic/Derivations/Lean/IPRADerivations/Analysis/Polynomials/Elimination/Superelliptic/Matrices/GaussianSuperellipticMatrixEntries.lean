import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticTail
import IPRADerivations.Analysis.RationalArithmetic.Fibers.GaussianRationalFiberRightInverse
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianDeterminantSignTransport
import IPRADerivations.Foundations.RuntimeCyclicPermutation

/-!
# Actual entries of the superelliptic multiplication matrix

The original polynomial companion shifts its stored descending rows and
multiplies the last row by f. A genuine QF induction follows one original
coefficient through every numerical companion stage. Its row is the actual
cyclic residue and its factor is the actual power at the quotient.
The original row-major matrix and native inverse index supply the final
entry observations. No curve root, matrix action, stage formula, or
nonzero/canonical-input law is assumed. Polynomial coefficient reflection
and weighted determinant degree are separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixEntries

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul qadd canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qnegative)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qadd_congr qmul_congr qsub_congr qmul_zero_right qzero_add)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion
  (rowShape normalized_evaluation companion companion_lookup output_evaluation nextRow next_inside next_outside)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (stage slot)
open LeanProofs.IPRA.Analysis.GaussianSuperellipticTail (tailRows)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF power_zero power_succ)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (evaluate_congr)
open LeanProofs.IPRA.Foundations.RuntimeCyclicPermutation (rotation wrap inverseIndex)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def A (G m i x : PTm n) : PTm n := evaluate (entry G (slot m i)) x
def storedValue (f G m a c j h x : PTm n) : PTm n := evaluate (entry (stage (tailRows f m c) G m a c j) h) x
def stage_value (f G m a c i j x : PTm n) : PTm n := storedValue f G m a c j (slot m (rotation m i j)) x

ipra_subst A
ipra_subst storedValue
ipra_subst stage_value

theorem stored_index_congr (f G m a c j x : PTm n) {h k : PTm n} (he : Γ ⊢[PRAAx] h ≐ k) : Γ ⊢[PRAAx]
    storedValue f G m a c j h x ≐ storedValue f G m a c j k x :=
  evaluate_congr (entry_congr (.eqRefl _) he) (.eqRefl _)
theorem positive_last (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] lt (pred m) m :=
  lt_congr (.eqRefl _) (Foundations.RuntimeWordAppend.positive_form _ hm).eqSymm (le_refl _)

theorem negative_product_subtraction (u v : PTm n) : Γ ⊢[PRAAx]
    qsub qzero (qmul u (qnegative v)) ≐ qmul u v := by
  refine (qsub_congr (.eqRefl _) (GaussianRationalFiberRightInverse.multiply_negative_right _ _)).eqTrans ?_
  change Γ ⊢[PRAAx] qadd qzero (qnegative (qnegative (qmul u v))) ≐ qmul u v
  exact (qadd_congr (.eqRefl _) (GaussianDeterminantSignTransport.negative_involution _
    (GaussianRationalHorner.qmul_canonical _ _))).eqTrans (qzero_add _ (GaussianRationalHorner.qmul_canonical _ _))

/-- An actual stored row before the last one is just the next old row. -/
theorem stored_inside (f G m a c j h x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hh : Γ ⊢[PRAAx] lt h (pred m)) : Γ ⊢[PRAAx]
    storedValue f G m a c (succ j) h x ≐ storedValue f G m a c j (succ h) x := by
  let S := stage (tailRows f m c) G m a c j
  let b := GaussianPolynomialMultiplicationMatrix.bound a c j
  have hnext : Γ ⊢[PRAAx] lt (succ h) m := lt_of_le_of_lt hh (positive_last _ hm)
  have hr : Γ ⊢[PRAAx] lt h m := lt_of_lt_of_le hh (le_of_lt (positive_last _ hm))
  have step := (evaluate_congr (entry_congr (GaussianPolynomialMultiplicationMatrix.stage_succ (Γ := Γ)
    (tailRows f m c) G m a c j) (.eqRefl h)) (.eqRefl x)).eqTrans
      ((evaluate_congr (companion_lookup _ _ _ _ _ _ hr) (.eqRefl _)).eqTrans
        (output_evaluation _ _ _ _ _ _ _ hm (GaussianSuperellipticTail.tail_shape _ _ _ hf)
          (GaussianPolynomialMultiplicationMatrix.stage_shape _ _ _ _ _ _ hG) hr))
  have hn : Γ ⊢[PRAAx] evaluate (nextRow S m b h) x ≐ storedValue f G m a c j (succ h) x :=
    (evaluate_congr (next_inside _ _ _ _ hnext) (.eqRefl _)).eqTrans (normalized_evaluation _ _)
  have hz : Γ ⊢[PRAAx] evaluate (entry (tailRows f m c) h) x ≐ qzero :=
    (evaluate_congr (GaussianSuperellipticTail.upper_row _ _ _ _ hh) (.eqRefl _)).eqTrans
      (GaussianRationalPolynomialBuffers.zeros_evaluation _ _)
  exact step.eqTrans ((qsub_congr hn (qmul_congr (.eqRefl _) hz)).eqTrans
    ((qsub_congr (.eqRefl _) (qmul_zero_right _)).eqTrans
      (GaussianRationalReconstruction.qsub_zero_right _ (GaussianRationalHorner.horner_canonical _ _ _))))

/-- The actual last stored row is oldTop*f; the two minus signs cancel. -/
theorem stored_last (f G m a c j x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    storedValue f G m a c (succ j) (pred m) x ≐ qmul (storedValue f G m a c j zero x) (evaluate f x) := by
  let S := stage (tailRows f m c) G m a c j
  let b := GaussianPolynomialMultiplicationMatrix.bound a c j
  have hr := positive_last _ hm
  have he := Foundations.RuntimeWordAppend.positive_form (Γ := Γ) m hm
  have outside : Γ ⊢[PRAAx] le m (succ (pred m)) := le_congr he.eqSymm (.eqRefl _) (le_refl _)
  have step := (evaluate_congr (entry_congr (GaussianPolynomialMultiplicationMatrix.stage_succ (Γ := Γ)
    (tailRows f m c) G m a c j) (.eqRefl (pred m))) (.eqRefl x)).eqTrans
      ((evaluate_congr (companion_lookup _ _ _ _ _ _ hr) (.eqRefl _)).eqTrans
        (output_evaluation _ _ _ _ _ _ _ hm (GaussianSuperellipticTail.tail_shape _ _ _ hf)
          (GaussianPolynomialMultiplicationMatrix.stage_shape _ _ _ _ _ _ hG) hr))
  have hn : Γ ⊢[PRAAx] evaluate (nextRow S m b (pred m)) x ≐ qzero :=
    (evaluate_congr (next_outside _ _ _ _ outside) (.eqRefl _)).eqTrans (GaussianRationalPolynomialBuffers.zeros_evaluation _ _)
  have hv : Γ ⊢[PRAAx] evaluate (entry (tailRows f m c) (pred m)) x ≐ qnegative (evaluate f x) :=
    (evaluate_congr (GaussianSuperellipticTail.last_row _ _ _) (.eqRefl _)).eqTrans
      (GaussianRationalGridCoefficientEquality.negative_evaluation _ _)
  exact step.eqTrans ((qsub_congr hn (qmul_congr (.eqRefl _) hv)).eqTrans (negative_product_subtraction _ _))

theorem next_no_wrap (m i j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] lt (succ (rotation m i j)) m) : Γ ⊢[PRAAx]
    (wrap m i (succ j) ≐ wrap m i j) ⋏ (rotation m i (succ j) ≐ succ (rotation m i j)) := by
  have e : Γ ⊢[PRAAx] succ j+i ≐ m*wrap m i j+succ (rotation m i j) :=
    (by ipra_ring : Γ ⊢[PRAAx] succ j+i ≐ succ (j+i)).eqTrans
      ((congrSucc (.andE₁ (Foundations.RuntimeCyclicPermutation.rotation_spec m i j hm))).eqTrans (by ipra_ring))
  exact Foundations.RuntimeWordAppend.divide_unique _ _ _ _ hm e h
theorem next_wrap (m i j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] succ (rotation m i j) ≐ m) : Γ ⊢[PRAAx]
    (wrap m i (succ j) ≐ succ (wrap m i j)) ⋏ (rotation m i (succ j) ≐ zero) := by
  have e : Γ ⊢[PRAAx] succ j+i ≐ m*wrap m i j+succ (rotation m i j) :=
    (by ipra_ring : Γ ⊢[PRAAx] succ j+i ≐ succ (j+i)).eqTrans
      ((congrSucc (.andE₁ (Foundations.RuntimeCyclicPermutation.rotation_spec m i j hm))).eqTrans (by ipra_ring))
  have e' : Γ ⊢[PRAAx] succ j+i ≐ m*succ (wrap m i j)+zero :=
    e.eqTrans ((congrAdd (.eqRefl _) h).eqTrans (by ipra_ring))
  exact Foundations.RuntimeWordAppend.divide_unique _ _ _ _ hm e' hm

theorem slot_no_wrap (m r : PTm n) (h : Γ ⊢[PRAAx] lt (succ r) m) : Γ ⊢[PRAAx]
    succ (slot m (succ r)) ≐ slot m r := by
  have span := eq_add_of_le h
  have e : Γ ⊢[PRAAx] m ≐ succ r+succ (slot m (succ r)) :=
    span.eqTrans (by unfold slot; ipra_ring)
  exact ((congrMonus e (.eqRefl (succ r))).eqTrans (add_monus' _ _)).eqSymm
theorem slot_before_last (m r : PTm n) (h : Γ ⊢[PRAAx] lt (succ r) m) : Γ ⊢[PRAAx]
    lt (slot m (succ r)) (pred m) := by
  have span : Γ ⊢[PRAAx] m ≐ succ (succ r+slot m (succ r)) :=
    (eq_add_of_le h).eqTrans (by unfold slot; ipra_ring)
  have e : Γ ⊢[PRAAx] pred m ≐ succ r+slot m (succ r) := (congrPred span).eqTrans (pred_succ _)
  have bound : Γ ⊢[PRAAx] lt (slot m (succ r)) (succ r+slot m (succ r)) :=
    lt_congr (add_zero _) (add_comm _ _) (Foundations.SequenceComposition.add_lt_left _ (zero_lt_succ r))
  exact lt_congr (.eqRefl _) e.eqSymm bound
theorem slot_wrap (m r : PTm n) (h : Γ ⊢[PRAAx] succ r ≐ m) : Γ ⊢[PRAAx] slot m r ≐ zero :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_self m)
theorem slot_zero (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] slot m zero ≐ pred m :=
  (GaussianPolynomialMultiplicationMatrix.slot_pred _ _ hm).eqTrans (monus_zero _)

theorem stage_base (f G m a c i x : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    stage_value f G m a c i zero x ≐ qmul (A G m i x) (power (evaluate f x) (wrap m i zero)) := by
  have d : Γ ⊢[PRAAx] (wrap m i zero ≐ zero) ⋏ (rotation m i zero ≐ i) :=
    Foundations.RuntimeWordAppend.divide_unique m (zero+i) zero i hm (by ipra_ring) hi
  have first : Γ ⊢[PRAAx] stage_value f G m a c i zero x ≐ storedValue f G m a c zero (slot m i) x :=
    stored_index_congr _ _ _ _ _ _ _ (congrMonus (.eqRefl _) (congrSucc (.andE₂ d)))
  have initial : Γ ⊢[PRAAx] storedValue f G m a c zero (slot m i) x ≐ A G m i x :=
    (evaluate_congr (entry_congr (GaussianPolynomialMultiplicationMatrix.stage_zero _ _ _ _ _) (.eqRefl _)) (.eqRefl _)).eqTrans
      ((evaluate_congr (GaussianPolynomialMultiplicationMatrix.normalized_rows_lookup _ _ _
        (GaussianPolynomialMultiplicationMatrix.slot_range _ _ hi)) (.eqRefl _)).eqTrans (normalized_evaluation _ _))
  have rhs : Γ ⊢[PRAAx] qmul (A G m i x) (power (evaluate f x) (wrap m i zero)) ≐ A G m i x :=
    (qmul_congr (.eqRefl _) ((congrAp2 powerF (.andE₁ d) (.eqRefl _)).eqTrans (power_zero _))).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _))
  exact first.eqTrans (initial.eqTrans rhs.eqSymm)

/-- The only incoming equality is the local QF induction hypothesis. -/
theorem stage_step (f G m a c i j x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hG : Γ ⊢[PRAAx] rowShape G m a)
    (h : Γ ⊢[PRAAx] stage_value f G m a c i j x ≐ qmul (A G m i x) (power (evaluate f x) (wrap m i j))) : Γ ⊢[PRAAx]
    stage_value f G m a c i (succ j) x ≐ qmul (A G m i x) (power (evaluate f x) (wrap m i (succ j))) := by
  let r := rotation m i j
  have range : Γ ⊢[PRAAx] le (succ r) m := .andE₂ (Foundations.RuntimeCyclicPermutation.rotation_spec _ _ _ hm)
  refine .orE (lt_or_eq_of_le range) ?_ ?_
  · let Δ := lt (succ r) m :: Γ
    have noWrap := next_no_wrap (Γ := Δ) m i j hm.wk Prf.hyp0
    have first : Δ ⊢[PRAAx] stage_value f G m a c i (succ j) x ≐
        storedValue f G m a c (succ j) (slot m (succ r)) x :=
      stored_index_congr _ _ _ _ _ _ _ (congrMonus (.eqRefl _) (congrSucc (.andE₂ noWrap)))
    have shift := stored_inside (Γ := Δ) f G m a c j (slot m (succ r)) x hm.wk hf.wk hG.wk
      (slot_before_last _ _ Prf.hyp0)
    have old := stored_index_congr (Γ := Δ) f G m a c j x (slot_no_wrap _ _ Prf.hyp0)
    exact first.eqTrans (shift.eqTrans (old.eqTrans (h.wk.eqTrans
      (qmul_congr (.eqRefl _) (congrAp2 powerF (Prf.andE₁ noWrap).eqSymm (.eqRefl _))))))
  · let Δ := (succ r ≐ m) :: Γ
    have carry := next_wrap (Γ := Δ) m i j hm.wk Prf.hyp0
    have first : Δ ⊢[PRAAx] stage_value f G m a c i (succ j) x ≐ storedValue f G m a c (succ j) (slot m zero) x :=
      stored_index_congr _ _ _ _ _ _ _ (congrMonus (.eqRefl _) (congrSucc (.andE₂ carry)))
    have last := stored_index_congr (Γ := Δ) f G m a c (succ j) x (slot_zero _ hm.wk)
    have old : Δ ⊢[PRAAx] storedValue f G m a c j zero x ≐ stage_value f G m a c i j x :=
      stored_index_congr _ _ _ _ _ _ _ (slot_wrap m r Prf.hyp0).eqSymm
    exact first.eqTrans (last.eqTrans ((stored_last _ _ _ _ _ _ _ hm.wk hf.wk hG.wk).eqTrans
      ((qmul_congr (old.eqTrans h.wk) (.eqRefl _)).eqTrans
        ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
          ((qmul_congr (.eqRefl _) (power_succ _ _).eqSymm).eqTrans
            (qmul_congr (.eqRefl _) (congrAp2 powerF (Prf.andE₁ carry).eqSymm (.eqRefl _))))))))

/-- All numerical stages are covered; only the original coefficient
index needs a bound. No curve equation or stage formula is a premise. -/
theorem stage_specialization (f G m a c i j x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    stage_value f G m a c i j x ≐ qmul (A G m i x) (power (evaluate f x) (wrap m i j)) := by
  have all : Γ ⊢[PRAAx] .all
      (stage_value (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift i) (var 0) (Syn.shift x) ≐
        qmul (A (Syn.shift G) (Syn.shift m) (Syn.shift i) (Syn.shift x))
          (power (evaluate (Syn.shift f) (Syn.shift x)) (wrap (Syn.shift m) (Syn.shift i) (var 0)))) := by
    ipra_qfind [subst_stage_value, subst_A, GaussianRationalHorner.subst_qmul, GaussianRationalHorner.subst_evaluate,
        GaussianRationalReciprocal.subst_power, Foundations.RuntimeCyclicPermutation.subst_wrap]
    · exact stage_base _ _ _ _ _ _ _ hm hi
    · have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
        simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift
      have fs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift f) ≐ succ (Syn.shift c) := by
        simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hf.shift
      have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
        simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hG.shift
      exact stage_step _ _ _ _ _ _ _ _ ms.wk fs.wk gs.wk Prf.hyp0
  simpa only [Fm.subst_eq,subst_stage_value,subst_A,GaussianRationalHorner.subst_qmul,
    GaussianRationalHorner.subst_evaluate,GaussianRationalReciprocal.subst_power,
    Foundations.RuntimeCyclicPermutation.subst_wrap,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem rotation_comm (m i j : PTm n) : Γ ⊢[PRAAx] rotation m i j ≐ rotation m j i :=
  congrAp2 remF (add_comm _ _) (.eqRefl _)
theorem wrap_comm (m i j : PTm n) : Γ ⊢[PRAAx] wrap m i j ≐ wrap m j i :=
  congrAp2 quoF (add_comm _ _) (.eqRefl _)

theorem matrix_entry_forward (f G m a c i j x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminantTerms.cell
      (GaussianPolynomialMultiplicationMatrix.matrix (tailRows f m c) G m a c) (rotation m i j) j) x ≐
        qmul (A G m i x) (power (evaluate f x) (wrap m i j)) :=
  (evaluate_congr (GaussianPolynomialMultiplicationMatrix.matrix_coefficient_polynomial _ _ _ _ _ _ _
    (.andE₂ (Foundations.RuntimeCyclicPermutation.rotation_spec _ _ _ hm)) hj) (.eqRefl _)).eqTrans
      ((GaussianPolynomialMultiplicationMatrix.matrix_entry_evaluation _ _ _ _ _ _ _ _).eqTrans
        (stage_specialization _ _ _ _ _ _ _ _ hm hf hG hi))

theorem inverse_row (m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    rotation m (inverseIndex m j r) j ≐ r :=
  (rotation_comm _ _ _).eqTrans (.andE₂ (Foundations.RuntimeCyclicPermutation.inverse_correct _ _ _ hj hr))

theorem matrix_entry (f G m a c r j x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminantTerms.cell
      (GaussianPolynomialMultiplicationMatrix.matrix (tailRows f m c) G m a c) r j) x ≐
        qmul (A G m (inverseIndex m j r) x) (power (evaluate f x) (wrap m (inverseIndex m j r) j)) :=
  (evaluate_congr (entry_congr (entry_congr (.eqRefl _) (inverse_row _ _ _ hr hj).eqSymm) (.eqRefl _)) (.eqRefl _)).eqTrans
    (matrix_entry_forward _ _ _ _ _ _ _ _ hm hf hG
      (.andE₁ (Foundations.RuntimeCyclicPermutation.inverse_correct _ _ _ hj hr)) hj)

theorem matrix_entry_wrap_cases (m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    (wrap m (inverseIndex m j r) j ≐ zero) ⋎ (wrap m (inverseIndex m j r) j ≐ one) :=
  Foundations.RuntimeCyclicPermutation.wrap_cases _ _ _
    (.andE₁ (Foundations.RuntimeCyclicPermutation.inverse_correct _ _ _ hj hr)) hj

theorem index_equation (m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    inverseIndex m j r+j ≐ r+m*wrap m (inverseIndex m j r) j :=
  (add_comm _ _).eqTrans ((Prf.andE₁ (Foundations.RuntimeCyclicPermutation.rotation_spec _ _ _
    (lt_of_le_of_lt (zero_le _) hr))).eqTrans
      ((congrAdd (.eqRefl _) (inverse_row _ _ _ hr hj)).eqTrans (add_comm _ _)))
theorem inverse_wrap_zero (m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hjr : Γ ⊢[PRAAx] le j r) : Γ ⊢[PRAAx]
    wrap m (inverseIndex m j r) j ≐ zero :=
  (wrap_comm _ _ _).eqTrans (Prf.andE₂ (Prf.andE₂ (Foundations.RuntimeCyclicPermutation.inverse_large_row _ _ _ hr hjr)))
theorem inverse_wrap_one (m r j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) (hrj : Γ ⊢[PRAAx] lt r j) : Γ ⊢[PRAAx]
    wrap m (inverseIndex m j r) j ≐ one :=
  (wrap_comm _ _ _).eqTrans (Prf.andE₂ (Prf.andE₂ (Foundations.RuntimeCyclicPermutation.inverse_small_row _ _ _ hj hrj)))

theorem matrix_entry_unwrapped (f G m a c r j x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m)
    (hjr : Γ ⊢[PRAAx] le j r) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminantTerms.cell
      (GaussianPolynomialMultiplicationMatrix.matrix (tailRows f m c) G m a c) r j) x ≐ A G m (inverseIndex m j r) x :=
  (matrix_entry _ _ _ _ _ _ _ _ hm hf hG hr hj).eqTrans
    ((qmul_congr (.eqRefl _) ((congrAp2 powerF (inverse_wrap_zero _ _ _ hr hjr) (.eqRefl _)).eqTrans (power_zero _))).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _)))
theorem matrix_entry_wrapped (f G m a c r j x : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m)
    (hrj : Γ ⊢[PRAAx] lt r j) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminantTerms.cell
      (GaussianPolynomialMultiplicationMatrix.matrix (tailRows f m c) G m a c) r j) x ≐
        qmul (A G m (inverseIndex m j r) x) (evaluate f x) :=
  (matrix_entry _ _ _ _ _ _ _ _ hm hf hG hr hj).eqTrans
    (qmul_congr (.eqRefl _) ((congrAp2 powerF (inverse_wrap_one _ _ _ hj hrj) (.eqRefl _)).eqTrans
      (GaussianRationalPowerAlgebra.power_one _ (GaussianRationalHorner.horner_canonical _ _ _))))

def rowsInput (f G m a c : PTm n) : Fm PTm n := le one m ⋏ ((length f ≐ succ c) ⋏ rowShape G m a)
def input (f G m a c r j : PTm n) : Fm PTm n := rowsInput f G m a c ⋏ (lt r m ⋏ lt j m)
def matrix (f G m a c : PTm n) : PTm n := GaussianPolynomialMultiplicationMatrix.matrix (tailRows f m c) G m a c
def entryPolynomial (f G m a c r j : PTm n) : PTm n := GaussianPolynomialDeterminantTerms.cell (matrix f G m a c) r j
def value (f G m a c r j x : PTm n) : PTm n := evaluate (entryPolynomial f G m a c r j) x
def expected (f G m _a _c r j x : PTm n) : PTm n :=
  qmul (A G m (inverseIndex m j r) x) (power (evaluate f x) (wrap m (inverseIndex m j r) j))
def certificate (f G m a c r j x : PTm n) : Fm PTm n :=
  lt (inverseIndex m j r) m ⋏ ((inverseIndex m j r+j ≐ r+m*wrap m (inverseIndex m j r) j) ⋏
    (((wrap m (inverseIndex m j r) j ≐ zero) ⋎ (wrap m (inverseIndex m j r) j ≐ one)) ⋏
      (value f G m a c r j x ≐ expected f G m a c r j x)))

ipra_subst rowsInput
ipra_subst input
ipra_subst matrix
ipra_subst entryPolynomial
ipra_subst value
ipra_subst expected
ipra_subst certificate

theorem matrix_entry_correct (f G m a c r j x : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    certificate f G m a c r j x := by
  have rows := Prf.andE₁ h
  have hr := Prf.andE₁ (Prf.andE₂ h)
  have hj := Prf.andE₂ (Prf.andE₂ h)
  exact .andI (.andE₁ (Foundations.RuntimeCyclicPermutation.inverse_correct _ _ _ hj hr))
    (.andI (index_equation _ _ _ hr hj) (.andI (matrix_entry_wrap_cases _ _ _ hr hj)
      (matrix_entry _ _ _ _ _ _ _ _ (.andE₁ rows) (.andE₁ (.andE₂ rows)) (.andE₂ (.andE₂ rows)) hr hj)))

/-! Six actual fields retain the original matrix, the computed original
coefficient index, wrap, original cell polynomial, and both scalar values. -/
def output (f G m a c r j x : PTm n) : PTm n := pairT (matrix f G m a c)
  (pairT (inverseIndex m j r) (pairT (wrap m (inverseIndex m j r) j)
    (pairT (entryPolynomial f G m a c r j) (pairT (value f G m a c r j x) (expected f G m a c r j x)))))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (f G m a c r j x : PTm n) : PTm n := app outputF ![f,G,m,a,c,r,j,x]
def fields (c : PTm n) (i : Fin 6) : PTm n :=
  ![fstT c,fstT (sndT c),fstT (sndT (sndT c)),fstT (sndT (sndT (sndT c))),
    fstT (sndT (sndT (sndT (sndT c)))),sndT (sndT (sndT (sndT (sndT c))))] i
ipra_subst output
ipra_subst run
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (c : PTm n) (i : Fin 6) :
    Syn.subst σ (fields c i) = fields (Syn.subst σ c) i :=
  subst_pairVectorField σ 5 c i
theorem program_at (f G m a c r j x : PTm n) : Γ ⊢[PRAAx] run f G m a c r j x ≐ output f G m a c r j x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![f,G,m,a,c,r,j,x]
theorem returned_fields (f G m a c r j x : PTm n) (i : Fin 6) : Γ ⊢[PRAAx]
    fields (run f G m a c r j x) i ≐
      ![matrix f G m a c,inverseIndex m j r,wrap m (inverseIndex m j r) j,
        entryPolynomial f G m a c r j,value f G m a c r j x,expected f G m a c r j x] i :=
  pairVectorField_eq 5 _ (program_at f G m a c r j x) i

theorem returned_equality (f G m a c r j x : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    fields (run f G m a c r j x) 4 ≐ fields (run f G m a c r j x) 5 :=
  (returned_fields _ _ _ _ _ _ _ _ 4).eqTrans
    ((Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (matrix_entry_correct _ _ _ _ _ _ _ _ h)))).eqTrans
      (returned_fields _ _ _ _ _ _ _ _ 5).eqSymm)
theorem returned_index_bound (f G m a c r j x : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    lt (fields (run f G m a c r j x) 1) m :=
  lt_congr (returned_fields _ _ _ _ _ _ _ _ 1).eqSymm (.eqRefl _) (Prf.andE₁ (matrix_entry_correct f G m a c r j x h))

/-! Every original polynomial, bound, matrix index, stage and query is
bound internally. The all-stage endpoint has no upper bound on j. -/
theorem actual_stored_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (rowsInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 6) (pred (var 2)) ⟶
      storedValue (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) (var 6) (var 7) ≐
        storedValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (succ (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (stored_inside _ _ _ _ _ _ _ _
    (.andE₁ Prf.hyp1) (.andE₁ (.andE₂ Prf.hyp1)) (.andE₂ (.andE₂ Prf.hyp1)) Prf.hyp0)))
theorem actual_stored_last_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (rowsInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      storedValue (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) (pred (var 2)) (var 6) ≐
        qmul (storedValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) zero (var 6)) (evaluate (var 0) (var 6))) :=
  closeUniv 7 (.impI (stored_last _ _ _ _ _ _ _
    (.andE₁ Prf.hyp0) (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))
theorem actual_all_stages_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (rowsInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (var 2) ⟶
      stage_value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
        qmul (A (var 1) (var 2) (var 5) (var 7)) (power (evaluate (var 0) (var 7)) (wrap (var 2) (var 5) (var 6)))) :=
  closeUniv 8 (.impI (.impI (stage_specialization _ _ _ _ _ _ _ _
    (.andE₁ Prf.hyp1) (.andE₁ (.andE₂ Prf.hyp1)) (.andE₂ (.andE₂ Prf.hyp1)) Prf.hyp0)))
theorem actual_matrix_forward_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (rowsInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (var 2) ⟶ lt (var 6) (var 2) ⟶
      evaluate (GaussianPolynomialDeterminantTerms.cell (matrix (var 0) (var 1) (var 2) (var 3) (var 4))
        (rotation (var 2) (var 5) (var 6)) (var 6)) (var 7) ≐
          qmul (A (var 1) (var 2) (var 5) (var 7)) (power (evaluate (var 0) (var 7)) (wrap (var 2) (var 5) (var 6)))) :=
  closeUniv 8 (.impI (.impI (.impI (matrix_entry_forward _ _ _ _ _ _ _ _
    (.andE₁ (Prf.hyp1.wk)) (.andE₁ (.andE₂ (Prf.hyp1.wk))) (.andE₂ (.andE₂ (Prf.hyp1.wk))) Prf.hyp1 Prf.hyp0))))
theorem actual_matrix_entries_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (.impI (matrix_entry_correct _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_index_equation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶ lt (var 2) (var 0) ⟶
      inverseIndex (var 0) (var 2) (var 1)+(var 2) ≐
        (var 1)+(var 0)*wrap (var 0) (inverseIndex (var 0) (var 2) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (index_equation _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_piecewise_entries_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      ((le (var 6) (var 5) ⟶ value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
        A (var 1) (var 2) (inverseIndex (var 2) (var 6) (var 5)) (var 7)) ⋏
          (lt (var 5) (var 6) ⟶ value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
            qmul (A (var 1) (var 2) (inverseIndex (var 2) (var 6) (var 5)) (var 7)) (evaluate (var 0) (var 7))))) :=
  closeUniv 8 (.impI (.andI
    (.impI (matrix_entry_unwrapped _ _ _ _ _ _ _ _ (.andE₁ (.andE₁ Prf.hyp1))
      (.andE₁ (.andE₂ (.andE₁ Prf.hyp1))) (.andE₂ (.andE₂ (.andE₁ Prf.hyp1)))
      (.andE₁ (.andE₂ Prf.hyp1)) (.andE₂ (.andE₂ Prf.hyp1)) Prf.hyp0))
    (.impI (matrix_entry_wrapped _ _ _ _ _ _ _ _ (.andE₁ (.andE₁ Prf.hyp1))
      (.andE₁ (.andE₂ (.andE₁ Prf.hyp1))) (.andE₂ (.andE₂ (.andE₁ Prf.hyp1)))
      (.andE₁ (.andE₂ Prf.hyp1)) (.andE₂ (.andE₂ Prf.hyp1)) Prf.hyp0))))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at _ _ _ _ _ _ _ _)
theorem actual_returned_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 4 ≐
        fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 5) :=
  closeUniv 8 (.impI (returned_equality _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_returned_index_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      lt (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 1) (var 2)) :=
  closeUniv 8 (.impI (returned_index_bound _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixEntries
