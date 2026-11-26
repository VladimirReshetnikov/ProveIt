import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalRowSpanPivotTransfer
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalTranslationAlgebra

/-!
# Actual forward row-span coefficients for one nonzero pivot

The off-pivot weights retain their original raw codes. The pivot weight
is the original pivot times its old weight plus the actual off-pivot
column sum. The checked row formulas and actual finite sums derive the
represented-column equality; no change-of-basis law is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRowSpanPivotForward

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalRowElimination (pivot inverse normalizedPivot eliminate input)
open GaussianRationalRowSpan (columnBody columnData combinationAt membership)
open GaussianRationalRowSpanPivotTransfer (offColumn maskBody mask_body_at data fields fields_at)
open GaussianTranslatedNonconstant (recode recode_eq)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def correction (A R u i p : PTm n) : PTm n :=
  qadd (qmul (pivot A i p) (entry u i)) (offColumn A R u i p)
def value (A R u i p r : PTm n) : PTm n := sel (eqb r i) (correction A R u i p) (entry u r)
def body : PTm 2 := value (fields (var 1) 0) (fields (var 1) 1) (fields (var 1) 2)
  (fields (var 1) 3) (fields (var 1) 4) (var 0)
def forward (A R u i p : PTm n) : PTm n := sequence body R (data A R u i p)

@[simp] theorem subst_correction {k : ℕ} (σ : Fin n → PTm k) (A R u i p : PTm n) :
    Syn.subst σ (correction A R u i p) = correction (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ p) := by simp [correction]
@[simp] theorem subst_value {k : ℕ} (σ : Fin n → PTm k) (A R u i p r : PTm n) :
    Syn.subst σ (value A R u i p r) = value (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ r) := by simp [value,sel]
@[simp] theorem subst_forward {k : ℕ} (σ : Fin n → PTm k) (A R u i p : PTm n) :
    Syn.subst σ (forward A R u i p) = forward (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ p) := by simp [forward]

theorem body_at (A R u i p r : PTm n) : Γ ⊢[PRAAx]
    inst2 body r (data A R u i p) ≐ value A R u i p r := by
  have last1 : ![fields (data A R u i p) 0,fields (data A R u i p) 1,fields (data A R u i p) 2,
    fields (data A R u i p) 3,fields (data A R u i p) 4,r] (5 : Fin 6) = r := rfl
  have last2 : ![A,R,u,i,p,r] (5 : Fin 6) = r := rfl
  simp only [body,inst2,subst_value,GaussianRationalRowSpanPivotTransfer.subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [subst_value,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,last1,last2,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![fields (data A R u i p) 0,fields (data A R u i p) 1,fields (data A R u i p) 2,
        fields (data A R u i p) 3,fields (data A R u i p) 4,r]) (σ' := ![A,R,u,i,p,r])
      (fun j => by
        fin_cases j
        · exact fields_at _ _ _ _ _ 0
        · exact fields_at _ _ _ _ _ 1
        · exact fields_at _ _ _ _ _ 2
        · exact fields_at _ _ _ _ _ 3
        · exact fields_at _ _ _ _ _ 4
        · exact .eqRefl _)
theorem forward_length (A R u i p : PTm n) : Γ ⊢[PRAAx] length (forward A R u i p) ≐ R := sequence_length _ _ _
theorem forward_lookup (A R u i p r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx]
    entry (forward A R u i p) r ≐ value A R u i p r :=
  (sequence_decode body (x := data A R u i p) hr).eqTrans (body_at _ _ _ _ _ _)
theorem forward_pivot (A R u i p : PTm n) (hi : Γ ⊢[PRAAx] lt i R) : Γ ⊢[PRAAx]
    entry (forward A R u i p) i ≐ correction A R u i p :=
  (forward_lookup _ _ _ _ _ _ hi).eqTrans (sel_one (eqb_of_eq (.eqRefl _)))
theorem forward_other (A R u i p r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (hne : Γ ⊢[PRAAx] neg (r ≐ i)) : Γ ⊢[PRAAx]
    entry (forward A R u i p) r ≐ entry u r :=
  (forward_lookup _ _ _ _ _ _ hr).eqTrans (sel_zero (eqb_of_ne hne))

theorem off_forward (A R u i p j : PTm n) : Γ ⊢[PRAAx]
    offColumn A R (forward A R u i p) i j ≐ offColumn A R u i j := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have l := mask_body_at (Γ := Δ) columnBody (Syn.shift i) (var 0)
    (columnData (Syn.shift A) (forward (Syn.shift A) (Syn.shift R) (Syn.shift u) (Syn.shift i) (Syn.shift p)) (Syn.shift j))
  have r := mask_body_at (Γ := Δ) columnBody (Syn.shift i) (var 0) (columnData (Syn.shift A) (Syn.shift u) (Syn.shift j))
  have e : Δ ⊢[PRAAx]
      inst2 (maskBody columnBody) (var 0) (pairT (Syn.shift i)
        (columnData (Syn.shift A) (forward (Syn.shift A) (Syn.shift R) (Syn.shift u) (Syn.shift i) (Syn.shift p)) (Syn.shift j))) ≐
      inst2 (maskBody columnBody) (var 0) (pairT (Syn.shift i) (columnData (Syn.shift A) (Syn.shift u) (Syn.shift j))) := by
    refine .orE (eq_or_ne (var 0) (Syn.shift i)) ?_ ?_
    · exact (l.wk.eqTrans (sel_one (eqb_of_eq Prf.hyp0))).eqTrans
        (r.wk.eqTrans (sel_one (eqb_of_eq Prf.hyp0))).eqSymm
    · exact (l.wk.eqTrans ((sel_zero (eqb_of_ne Prf.hyp0)).eqTrans
        ((GaussianRationalRowSpan.column_body_at _ _ _ _).eqTrans
          (qmul_congr (forward_other _ _ _ _ _ _ Prf.hyp1 Prf.hyp0) (.eqRefl _))))).eqTrans
            (r.wk.eqTrans ((sel_zero (eqb_of_ne Prf.hyp0)).eqTrans (GaussianRationalRowSpan.column_body_at _ _ _ _))).eqSymm
  simpa only [Δ,Syn.shift,subst_pairT,GaussianRationalRowSpan.subst_columnData,subst_forward] using e

theorem pivot_row_restore (A i p j : PTm n) (h : Γ ⊢[PRAAx] neg (pivot A i p ≐ qzero)) : Γ ⊢[PRAAx]
    qmul (pivot A i p) (normalizedPivot A i p j) ≐ recode (cell A i j) :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr (GaussianRationalRowElimination.pivot_inverse A i p h) (.eqRefl _)).eqTrans
      (GaussianRationalFiniteProduct.raw_one_left _))

theorem normalized_weight_restore (A u i p j : PTm n) (h : Γ ⊢[PRAAx] neg (pivot A i p ≐ qzero)) : Γ ⊢[PRAAx]
    qmul (normalizedPivot A i p j) (qmul (pivot A i p) (entry u i)) ≐ qmul (entry u i) (cell A i j) :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
      ((qmul_congr (pivot_row_restore A i p j h) (.eqRefl _)).eqTrans
        ((GaussianRationalSyntheticCoefficientValues.qmul_recode_left _ _).eqTrans
          (GaussianRationalPowerAlgebra.qmul_commutative _ _))))

theorem cancel_correction (a s z : PTm n) : Γ ⊢[PRAAx]
    qmul (qsub (qadd a s) s) z ≐ qmul z a :=
  (qmul_congr (qsub_congr (GaussianReciprocalHorner.qadd_commutative _ _) (.eqRefl _)) (.eqRefl _)).eqTrans
    (GaussianRationalTranslationAlgebra.cancel_shift_product s a z)

theorem column_forward (A R N u i p j : PTm n) (h : Γ ⊢[PRAAx] input A R N i p)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt (eliminate A R N i p) R (forward A R u i p) j ≐ combinationAt A R u j := by
  have hi := Prf.andE₁ (Prf.andE₂ h)
  have hn := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have replacement : Γ ⊢[PRAAx]
      qmul (qsub (entry (forward A R u i p) i) (offColumn A R (forward A R u i p) i p))
        (normalizedPivot A i p j) ≐ qmul (entry u i) (cell A i j) :=
    (qmul_congr (qsub_congr (forward_pivot A R u i p hi) (off_forward A R u i p p)) (.eqRefl _)).eqTrans
      ((cancel_correction _ _ _).eqTrans (normalized_weight_restore A u i p j hn))
  have oldTerm : Γ ⊢[PRAAx] recode (inst2 columnBody i (columnData A u j)) ≐ qmul (entry u i) (cell A i j) :=
    (GaussianTranslatedNonconstant.recode_congr (GaussianRationalRowSpan.column_body_at _ _ _ _)).eqTrans
      (recode_eq _ (GaussianRationalHorner.qmul_canonical _ _))
  exact (GaussianRationalRowSpanPivotTransfer.reduced_combination A R N (forward A R u i p) i p j hi hj).eqTrans
    ((qadd_congr (off_forward A R u i p j) replacement).eqTrans
      ((qadd_congr (.eqRefl _) oldTerm).eqSymm.eqTrans
        (GaussianRationalRowSpanPivotTransfer.sum_decompose columnBody R i (columnData A u j) hi).eqSymm))

theorem membership_forward (A R N u i p v : PTm n) (hInput : Γ ⊢[PRAAx] input A R N i p)
    (hm : Γ ⊢[PRAAx] membership A R N u v) : Γ ⊢[PRAAx]
    membership (eliminate A R N i p) R N (forward A R u i p) v := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p) := by
    simpa only [Fm.shift,GaussianRationalRowElimination.subst_input,Syn.shift] using hInput.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift u) (Syn.shift v) := by
    simpa only [Fm.shift,GaussianRationalRowSpan.subst_membership,Syn.shift] using hm.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have source := GaussianRationalRowSpan.membership_at (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N)
    (Syn.shift u) (Syn.shift v) (var 0) ms.wk Prf.hyp0
  have target := (GaussianRationalRowSpan.combination_lookup (Γ := Δ)
    (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p)) (Syn.shift R)
      (Syn.shift N) (forward (Syn.shift A) (Syn.shift R) (Syn.shift u) (Syn.shift i) (Syn.shift p)) (var 0) Prf.hyp0).eqTrans
        ((column_forward _ _ _ _ _ _ _ hs.wk Prf.hyp0).eqTrans
          (GaussianRationalRowSpan.combination_lookup _ _ _ _ _ Prf.hyp0).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalRowElimination.subst_eliminate,subst_forward] using
    GaussianRationalValueEquality.value_equal_trans _ _ _ source (GaussianRationalValueEquality.value_equal_of_code target.eqSymm)

def outputF : PR 5 := PTm.toPR (forward (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A R u i p : PTm n) : PTm n := app outputF ![A,R,u,i,p]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (A R u i p : PTm n) :
    Syn.subst σ (run A R u i p) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ p) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl
theorem program_at (A R u i p : PTm n) : Γ ⊢[PRAAx] run A R u i p ≐ forward A R u i p := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (forward (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,R,u,i,p]
theorem returned_length (A R u i p : PTm n) : Γ ⊢[PRAAx] length (run A R u i p) ≐ R :=
  (congrFst (program_at A R u i p)).eqTrans (forward_length A R u i p)
theorem returned_pivot (A R u i p : PTm n) (hi : Γ ⊢[PRAAx] lt i R) : Γ ⊢[PRAAx]
    entry (run A R u i p) i ≐ correction A R u i p :=
  (entry_congr (program_at A R u i p) (.eqRefl _)).eqTrans (forward_pivot A R u i p hi)
theorem returned_other (A R u i p r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (hne : Γ ⊢[PRAAx] neg (r ≐ i)) : Γ ⊢[PRAAx]
    entry (run A R u i p) r ≐ entry u r :=
  (entry_congr (program_at A R u i p) (.eqRefl _)).eqTrans (forward_other A R u i p r hr hne)
theorem returned_column_forward (A R N u i p j : PTm n) (h : Γ ⊢[PRAAx] input A R N i p)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt (eliminate A R N i p) R (run A R u i p) j ≐ combinationAt A R u j :=
  (GaussianRationalFiniteSum.sum_index_congr columnBody (.eqRefl R)
    (congrPairT (.eqRefl (eliminate A R N i p)) (congrPairT (program_at A R u i p) (.eqRefl j)))).eqTrans
      (column_forward A R N u i p j h hj)

theorem actual_forward_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (forward (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 1) := closeUniv 5 (forward_length _ _ _ _ _)
theorem actual_forward_pivot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 1) ⟶ entry (forward (var 0) (var 1) (var 2) (var 3) (var 4)) (var 3) ≐
      correction (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (.impI (forward_pivot _ _ _ _ _ Prf.hyp0))
theorem actual_forward_other_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 1) ⟶ neg (var 5 ≐ var 3) ⟶
      entry (forward (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐ entry (var 2) (var 5)) :=
  closeUniv 6 (.impI (.impI (forward_other _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_column_forward_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 4) (var 5) ⟶ lt (var 6) (var 2) ⟶
      combinationAt (eliminate (var 0) (var 1) (var 2) (var 4) (var 5)) (var 1)
        (forward (var 0) (var 1) (var 3) (var 4) (var 5)) (var 6) ≐ combinationAt (var 0) (var 1) (var 3) (var 6)) :=
  closeUniv 7 (.impI (.impI (column_forward _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_membership_forward_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 4) (var 5) ⟶ membership (var 0) (var 1) (var 2) (var 3) (var 6) ⟶
      membership (eliminate (var 0) (var 1) (var 2) (var 4) (var 5)) (var 1) (var 2)
        (forward (var 0) (var 1) (var 3) (var 4) (var 5)) (var 6)) :=
  closeUniv 7 (.impI (.impI (membership_forward _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ forward (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_column_forward_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 4) (var 5) ⟶ lt (var 6) (var 2) ⟶
      combinationAt (eliminate (var 0) (var 1) (var 2) (var 4) (var 5)) (var 1)
        (run (var 0) (var 1) (var 3) (var 4) (var 5)) (var 6) ≐ combinationAt (var 0) (var 1) (var 3) (var 6)) :=
  closeUniv 7 (.impI (.impI (returned_column_forward _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalRowSpanPivotForward
