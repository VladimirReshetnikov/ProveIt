import IPRADerivations.Analysis.GaussianPolynomialMonicNorm
import IPRADerivations.Analysis.GaussianRationalGridCoefficientEquality
import IPRADerivations.Foundations.RuntimeWordAppend

/-!
# The stored coefficient rows for a superelliptic equation

For `Y^m - f(X)`, the stored nonleading rows consist of `m-1` zero
buffers and then the actual negated buffer for `f`. This is the
descending order consumed by the original multiplication matrix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (pred monus)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition
  (length append append_length append_left append_right_at subst_length)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction
  (singleton singleton_length singleton_lookup evaluate_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (zeros zeros_length zeros_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalGridCoefficientEquality
  (negativePolynomial negative_length negative_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qzero)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion (rowShape values values_lookup)
open scoped Fm
open Syn

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zeroRows (m c : PTm n) : PTm n :=
  sequence (var 1) (pred m) (zeros (succ c))

def tailRows (f m c : PTm n) : PTm n :=
  append (zeroRows m c) (singleton (negativePolynomial f))

def superellipticNorm (f G m a c : PTm n) : PTm n :=
  GaussianPolynomialMonicNorm.norm (tailRows f m c) G m a c

@[simp] theorem subst_zeroRows {l : ℕ} (σ : Fin n → PTm l) (m c : PTm n) :
    Syn.subst σ (zeroRows m c) = zeroRows (Syn.subst σ m) (Syn.subst σ c) := by
  simp [zeroRows]

@[simp] theorem subst_tailRows {l : ℕ} (σ : Fin n → PTm l) (f m c : PTm n) :
    Syn.subst σ (tailRows f m c) =
      tailRows (Syn.subst σ f) (Syn.subst σ m) (Syn.subst σ c) := by
  simp [tailRows]

theorem zero_rows_length (m c : PTm n) : Γ ⊢[PRAAx] length (zeroRows m c) ≐ pred m :=
  sequence_length _ _ _

theorem tail_rows_length (f m c : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] length (tailRows f m c) ≐ m :=
  (append_length _ _).eqTrans
    ((congrAdd (zero_rows_length m c) (singleton_length _)).eqTrans
      ((succ_eq_add_one _).eqSymm.eqTrans (Foundations.RuntimeWordAppend.positive_form _ hm).eqSymm))

theorem upper_row (f m c j : PTm n) (hj : Γ ⊢[PRAAx] lt j (pred m)) :
    Γ ⊢[PRAAx] entry (tailRows f m c) j ≐ zeros (succ c) := by
  have h₁ := append_left (b := singleton (negativePolynomial f))
    (lt_congr (.eqRefl _) (zero_rows_length m c).eqSymm hj)
  have h₂ : Γ ⊢[PRAAx] entry (zeroRows m c) j ≐ zeros (succ c) := by
    simpa [zeroRows,inst2] using sequence_decode (var 1 : PTm 2) (x := zeros (succ c)) hj
  exact h₁.eqTrans h₂

theorem last_row (f m c : PTm n) :
    Γ ⊢[PRAAx] entry (tailRows f m c) (pred m) ≐ negativePolynomial f := by
  let a := zeroRows m c
  let b := singleton (negativePolynomial f)
  let j := pred m
  have e : Γ ⊢[PRAAx] length a ≐ j := zero_rows_length _ _
  have eb : Γ ⊢[PRAAx] length b ≐ one := singleton_length _
  have hlt : Γ ⊢[PRAAx] lt j (length a + length b) :=
    lt_congr (.eqRefl _) ((succ_eq_add_one j).eqTrans (congrAdd e.eqSymm eb.eqSymm)) (le_refl _)
  exact (append_right_at (le_congr e.eqSymm (.eqRefl _) (le_refl j)) hlt).eqTrans
    ((Foundations.SequenceComposition.entry_congr (.eqRefl _) ((congrMonus (.eqRefl j) e).eqTrans (monus_self j))).eqTrans
      (singleton_lookup _))

theorem row_length_at (f m c j : PTm n)
    (hf : Γ ⊢[PRAAx] length f ≐ succ c) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] length (entry (tailRows f m c) j) ≐ succ c := by
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le j) hj
  have hs : Γ ⊢[PRAAx] le (succ j) (succ (pred m)) :=
    le_congr (.eqRefl _) (Foundations.RuntimeWordAppend.positive_form _ hm) hj
  have hle : Γ ⊢[PRAAx] le j (pred m) :=
    (succ_monus_succ j (pred m)).eqSymm.eqTrans hs
  refine .orE (lt_or_eq_of_le hle) ?_ ?_
  · exact (congrFst (upper_row _ _ _ _ Prf.hyp0)).eqTrans (zeros_length _)
  · exact (congrFst (Foundations.SequenceComposition.entry_congr (.eqRefl _) Prf.hyp0)).eqTrans
      ((congrFst (last_row _ _ _)).eqTrans ((negative_length _).eqTrans hf.wk))

theorem tail_shape (f m c : PTm n) (hf : Γ ⊢[PRAAx] length f ≐ succ c) :
    Γ ⊢[PRAAx] rowShape (tailRows f m c) m c := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift f) ≐ succ (Syn.shift c) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hf.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_tailRows] using
    row_length_at (Syn.shift f) (Syn.shift m) (Syn.shift c) (var 0) hs.wk Prf.hyp0

theorem upper_value (f m c x j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hj : Γ ⊢[PRAAx] lt j (pred m)) :
    Γ ⊢[PRAAx] entry (values (tailRows f m c) m x) j ≐ qzero :=
  (values_lookup _ _ _ _ (lt_of_lt_of_le hj
      (le_congr (.eqRefl _) (Foundations.RuntimeWordAppend.positive_form _ hm).eqSymm (le_succ_self _)))).eqTrans
    ((evaluate_congr (upper_row _ _ _ _ hj) (.eqRefl _)).eqTrans (zeros_evaluation _ _))

theorem last_value (f m c x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] entry (values (tailRows f m c) m x) (pred m) ≐
      GaussianRationalMetric.qnegative (evaluate f x) :=
  (values_lookup _ _ _ _ (lt_congr (.eqRefl _)
      (Foundations.RuntimeWordAppend.positive_form _ hm).eqSymm (le_refl _))).eqTrans
    ((evaluate_congr (last_row _ _ _) (.eqRefl _)).eqTrans (negative_evaluation _ _))

theorem superelliptic_norm_input (f G m a c : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) :
    Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input (tailRows f m c) G m a c :=
  .andI hm (.andI (tail_shape f m c hf) hG)

theorem actual_tail_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 2) ⟶ rowShape (tailRows (var 0) (var 1) (var 2)) (var 1) (var 2)) :=
  closeUniv 3 (.impI (tail_shape _ _ _ Prf.hyp0))

theorem actual_last_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ entry (values (tailRows (var 0) (var 1) (var 2)) (var 1) (var 3)) (pred (var 1)) ≐
      GaussianRationalMetric.qnegative (evaluate (var 0) (var 3))) :=
  closeUniv 4 (.impI (last_value _ _ _ _ Prf.hyp0))

open GaussianPolynomialMonicCompanion (monicValues monic_head monic_tail monic_length subst_monicValues)
open GaussianRationalHorner (horner hornerF horner_zero horner_succ subst_horner qadd qmul qmul_canonical)
open GaussianRationalSyntheticDivision
  (qone qone_canonical qadd_congr qmul_congr qmul_zero_left qzero_add)
open GaussianRationalReciprocal (power powerF power_zero power_succ subst_power)
open GaussianReciprocalHorner (qadd_zero_right)

theorem horner_head (f m c x y : PTm n) :
    Γ ⊢[PRAAx] horner (monicValues (tailRows f m c) m x) y one ≐ power y zero :=
  (horner_succ _ _ zero).eqTrans
    ((qadd_congr ((qmul_congr (horner_zero _ _) (.eqRefl _)).eqTrans (qmul_zero_left _))
      (monic_head _ _ _)).eqTrans
      ((qzero_add _ qone_canonical).eqTrans (power_zero y).eqSymm))

theorem horner_zero_row (f m c x y j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (h : Γ ⊢[PRAAx] horner (monicValues (tailRows f m c) m x) y (succ j) ≐ power y j) :
    Γ ⊢[PRAAx] horner (monicValues (tailRows f m c) m x) y (succ (succ j)) ≐ power y (succ j) := by
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le _) hj
  have hh : Γ ⊢[PRAAx] le (succ (succ j)) (succ (pred m)) :=
    le_congr (.eqRefl _) (Foundations.RuntimeWordAppend.positive_form _ hm) hj
  have hrow : Γ ⊢[PRAAx] lt j (pred m) :=
    (succ_monus_succ (succ j) (pred m)).eqSymm.eqTrans hh
  have hz : Γ ⊢[PRAAx] entry (monicValues (tailRows f m c) m x) (succ j) ≐ qzero :=
    (monic_tail _ _ _ _ (lt_of_le_of_lt (le_succ_self _) hj)).eqTrans
      ((evaluate_congr (upper_row _ _ _ _ hrow) (.eqRefl _)).eqTrans (zeros_evaluation _ _))
  exact (horner_succ _ _ _).eqTrans
    ((qadd_congr (qmul_congr h (.eqRefl _)) hz).eqTrans
      ((qadd_zero_right _ (qmul_canonical _ _)).eqTrans (power_succ y j).eqSymm))

/-- Every prefix before the last coefficient consists of the leading one
followed by zeros. The induction stays within the original row count. -/
theorem horner_before_last (f m c x y j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] horner (monicValues (tailRows f m c) m x) y (succ j) ≐ power y j := by
  have all : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift m) ⟶
    horner (monicValues (tailRows (Syn.shift f) (Syn.shift m) (Syn.shift c)) (Syn.shift m) (Syn.shift x))
      (Syn.shift y) (succ (var 0)) ≐ power (Syn.shift y) (var 0)) := by
    refine PRA.qfInd _ ⟨lt_QF _ _,trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp,Fm.subst_eq,subst_lt,subst_horner,subst_monicValues,subst_tailRows,
        subst_power,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (horner_head _ _ _ _ _)
    · simp only [Fm.subst_imp,Fm.subst_eq,subst_lt,subst_horner,subst_monicValues,subst_tailRows,
        subst_power,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact horner_zero_row _ _ _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (lt_of_le_of_lt (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] lt j m ⟶ horner (monicValues (tailRows f m c) m x) y (succ j) ≐ power y j := by
    simpa only [Fm.subst_imp,Fm.subst_eq,subst_lt,subst_horner,subst_monicValues,subst_tailRows,
      subst_power,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

/-- The actual original monic evaluator specializes to the source equation
`Y^m - f(X)` at arbitrary raw Gaussian rational queries. -/
theorem curve_evaluation (f m c x y : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] evaluate (monicValues (tailRows f m c) m x) y ≐
      GaussianRationalMetric.qsub (power y m) (evaluate f x) := by
  let F := tailRows f m c
  let C := monicValues F m x
  let j := pred m
  have e : Γ ⊢[PRAAx] m ≐ succ j := Foundations.RuntimeWordAppend.positive_form _ hm
  have hj : Γ ⊢[PRAAx] lt j m := lt_congr (.eqRefl _) e.eqSymm (le_refl _)
  have pre : Γ ⊢[PRAAx] horner C y m ≐ power y j :=
    (congrAp3 hornerF e (.eqRefl _) (.eqRefl _)).eqTrans (horner_before_last _ _ _ _ _ _ hj)
  have last : Γ ⊢[PRAAx] entry C m ≐ GaussianRationalMetric.qnegative (evaluate f x) :=
    (Foundations.SequenceComposition.entry_congr (.eqRefl _) e).eqTrans
      ((monic_tail _ _ _ _ hj).eqTrans
        ((evaluate_congr (last_row _ _ _) (.eqRefl _)).eqTrans (negative_evaluation _ _)))
  have hp : Γ ⊢[PRAAx] power y m ≐ qmul (power y j) y :=
    (congrAp2 powerF e (.eqRefl _)).eqTrans (power_succ y j)
  exact (congrAp3 hornerF (monic_length F m x) (.eqRefl _) (.eqRefl _)).eqTrans
    ((horner_succ _ _ _).eqTrans (qadd_congr ((qmul_congr pre (.eqRefl _)).eqTrans hp.eqSymm) last))

theorem actual_curve_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ evaluate (monicValues (tailRows (var 0) (var 1) (var 2)) (var 1) (var 3)) (var 4) ≐
      GaussianRationalMetric.qsub (power (var 4) (var 1)) (evaluate (var 0) (var 3))) :=
  closeUniv 5 (.impI (curve_evaluation _ _ _ _ _ Prf.hyp0))

theorem curve_equality (f m c x y : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] Fm.iff
      (evaluate (monicValues (tailRows f m c) m x) y ≐ qzero)
      (power y m ≐ evaluate f x) := by
  let a := power y m
  let b := evaluate f x
  have e := curve_evaluation f m c x y hm
  have eqzero := GaussianRationalValueEquality.recode_eq_iff_difference_zero (Γ := Γ) a b
  have ca := GaussianRationalReciprocal.power_canonical (Γ := Γ) y m
  have cb := GaussianRationalHorner.horner_canonical (Γ := Γ) f x (length f)
  have ar := GaussianTranslatedNonconstant.recode_eq a ca
  have br := GaussianTranslatedNonconstant.recode_eq b cb
  refine .iffI (.impI ?_) (.impI ?_)
  · exact ar.wk.eqSymm.eqTrans
      ((eqzero.wk.iffMpr (e.wk.eqSymm.eqTrans Prf.hyp0)).eqTrans br.wk)
  · exact e.wk.eqTrans (eqzero.wk.iffMp (GaussianTranslatedNonconstant.recode_congr Prf.hyp0))

theorem actual_curve_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ Fm.iff
      (evaluate (monicValues (tailRows (var 0) (var 1) (var 2)) (var 1) (var 3)) (var 4) ≐ qzero)
      (power (var 4) (var 1) ≐ evaluate (var 0) (var 3))) :=
  closeUniv 5 (.impI (curve_equality _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticTail
