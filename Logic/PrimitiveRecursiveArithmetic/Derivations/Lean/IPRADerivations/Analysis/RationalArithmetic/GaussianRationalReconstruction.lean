import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalLinearProduct
import IPRADerivations.Analysis.Polynomials.GaussianReciprocalHorner
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual product polynomial reconstructed from a runtime root list

The coefficient program folds backwards from the literal polynomial one.
Each step multiplies the current actual coefficient list by the linear factor
at the next original root lookup. A separate scalar program folds the same
factors in their original order. Their evaluation identity and the coefficient
length, canonical storage and monicity are derived, rather than supplied.
All root codes, counters and degrees are internal; repetitions are allowed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalReconstruction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical evaluate horner)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qone_canonical canonicalCoefficients qadd_congr qmul_congr qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalDeflation
  (singleton subst_singleton singleton_length singleton_entry remaining remaining_step)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct (linear subst_linear linear_length linear_canonical)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (S N : PTm n) : PTm n := pairT S N
def initialBody : PTm 1 := singleton qone
def stepBody : PTm 3 := linear (var 1)
  (entry (fstT (var 2)) (monus (sndT (var 2)) (succ (var 0)))) (length (var 1))
def reconstructF : PR 2 := rec2 initialBody stepBody
def reconstruct (S N k : PTm n) : PTm n := ap2 reconstructF k (data S N)
def suffix (S N j : PTm n) : PTm n := reconstruct S N (remaining N j)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (S N : PTm n) :
    Syn.subst σ (data S N) = data (Syn.subst σ S) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_reconstruct {m : ℕ} (σ : Fin n → PTm m) (S N k : PTm n) :
    Syn.subst σ (reconstruct S N k) = reconstruct (Syn.subst σ S) (Syn.subst σ N) (Syn.subst σ k) := by
  simp only [reconstruct,subst_ap2,subst_data]
@[simp] theorem subst_suffix {m : ℕ} (σ : Fin n → PTm m) (S N j : PTm n) :
    Syn.subst σ (suffix S N j) = suffix (Syn.subst σ S) (Syn.subst σ N) (Syn.subst σ j) := by simp [suffix]

theorem linear_congr {C C' z z' N N' : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hz : Γ ⊢[PRAAx] z ≐ z') (hN : Γ ⊢[PRAAx] N ≐ N') :
    Γ ⊢[PRAAx] linear C z N ≐ linear C' z' N' := by
  ipra_congr (linear (var 0) (var 1) (var 2) : PTm 3) with [hC, hz, hN]

theorem reconstruct_index_congr (S N : PTm n) {k k' : PTm n} (h : Γ ⊢[PRAAx] k ≐ k') :
    Γ ⊢[PRAAx] reconstruct S N k ≐ reconstruct S N k' := congrAp2 reconstructF h (.eqRefl _)

theorem reconstruct_zero (S N : PTm n) : Γ ⊢[PRAAx] reconstruct S N zero ≐ singleton qone := by
  simpa only [reconstruct,reconstructF,initialBody,subst_singleton,GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) initialBody stepBody (data S N)

theorem reconstruct_succ (S N k : PTm n) : Γ ⊢[PRAAx]
    reconstruct S N (succ k) ≐ linear (reconstruct S N k) (entry S (monus N (succ k))) (length (reconstruct S N k)) := by
  have h := rec2_succ (Γ := Γ) initialBody stepBody k (data S N)
  simp only [stepBody,subst_linear,subst_entry,subst_fstT,subst_sndT,PTm.subst_monus,
    ConciseIPRA.PTm.subst_succ,subst_length,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h
  exact h.eqTrans (linear_congr (.eqRefl _)
    (entry_congr (fst_pair _ _) (congrMonus (snd_pair _ _) (.eqRefl _))) (.eqRefl _))

theorem reconstruct_length (S N k : PTm n) : Γ ⊢[PRAAx] length (reconstruct S N k) ≐ succ k := by
  have all : Γ ⊢[PRAAx] .all (length (reconstruct (Syn.shift S) (Syn.shift N) (var 0)) ≐ succ (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_length,subst_reconstruct,ConciseIPRA.PTm.subst_succ,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (congrFst (reconstruct_zero S N)).eqTrans (singleton_length _)
    · simp only [Fm.subst_eq,subst_length,subst_reconstruct,ConciseIPRA.PTm.subst_succ,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (reconstruct_succ _ _ _)).eqTrans ((linear_length _ _ _).eqTrans (congrSucc Prf.hyp0))
  simpa only [Fm.subst_eq,subst_length,subst_reconstruct,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all

theorem singleton_canonical : Γ ⊢[PRAAx] canonicalCoefficients (singleton (qone : PTm n)) := by
  refine .allI (.impI ?_)
  have hi : lt (var 0) (length (Syn.shift (singleton (qone : PTm n)))) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) one :=
    lt_congr (.eqRefl _) (singleton_length _)
      (by simpa only [Syn.shift,subst_singleton,GaussianRationalSyntheticDivision.subst_qone] using Prf.hyp0)
  have h := sequence_decode (var 1 : PTm 2) (x := (qone : PTm (n+1))) hi
  have lookup : lt (var 0) (length (Syn.shift (singleton (qone : PTm n)))) :: Γ.map Fm.shift ⊢[PRAAx]
      entry (singleton qone) (var 0) ≐ qone := by
    simpa only [GaussianRationalDeflation.singleton,inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using h
  simpa only [Syn.shift,subst_singleton,GaussianRationalSyntheticDivision.subst_qone] using
    GaussianRationalHorner.canonical_congr lookup qone_canonical

theorem reconstruct_canonical (S N k : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (reconstruct S N k) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · exact GaussianRationalDeflation.coefficients_congr
      ((reconstruct_index_congr S N Prf.hyp0).eqTrans (reconstruct_zero S N)) singleton_canonical
  · have h : (k ≐ succ (PTm.pred k)) :: Γ ⊢[PRAAx] reconstruct S N k ≐
        linear (reconstruct S N (PTm.pred k)) (entry S (monus N (succ (PTm.pred k))))
          (length (reconstruct S N (PTm.pred k))) :=
      (reconstruct_index_congr S N Prf.hyp0).eqTrans (reconstruct_succ S N (PTm.pred k))
    exact GaussianRationalDeflation.coefficients_congr h (linear_canonical _ _ _)

/-- Subtracting actual zero recovers a canonical original point. -/
theorem qsub_zero_right (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] qsub q qzero ≐ q :=
  (qsub_congr (GaussianRationalSyntheticDivision.qzero_add q hq).eqSymm (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel qzero q hq)

theorem linear_monic (C z M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx] entry (linear C z M) zero ≐ qone := by
  have leading := GaussianRationalLinearProduct.padded_inside C M zero hM
  have delayed := GaussianRationalLinearProduct.delayed_zero (Γ := Γ) C M
  have coefficient : Γ ⊢[PRAAx] GaussianRationalLinearProduct.coefficient C z M zero ≐ qone :=
    (qsub_congr (leading.eqTrans hMonic)
      ((qmul_congr delayed (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left z))).eqTrans
        (qsub_zero_right qone qone_canonical)
  exact (GaussianRationalLinearProduct.linear_lookup C z M zero (zero_le _)).eqTrans coefficient

theorem reconstruct_monic (S N k : PTm n) : Γ ⊢[PRAAx] entry (reconstruct S N k) zero ≐ qone := by
  have all : Γ ⊢[PRAAx] .all (entry (reconstruct (Syn.shift S) (Syn.shift N) (var 0)) zero ≐ qone) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_entry,subst_reconstruct,ConciseIPRA.PTm.subst_zero,
        GaussianRationalSyntheticDivision.subst_qone,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (entry_congr (reconstruct_zero S N) (.eqRefl _)).eqTrans (singleton_entry _)
    · simp only [Fm.subst_eq,subst_entry,subst_reconstruct,ConciseIPRA.PTm.subst_zero,
        GaussianRationalSyntheticDivision.subst_qone,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      have pos : Γ.map Fm.shift ⊢[PRAAx] le one (length (reconstruct (Syn.shift S) (Syn.shift N) (var 0))) := le_congr (.eqRefl one) (reconstruct_length (Syn.shift S) (Syn.shift N) (var 0)).eqSymm
        (le_of_eq_add (d := (var 0 : PTm (n+1))) (by ipra_ring))
      exact (entry_congr (reconstruct_succ _ _ _) (.eqRefl _)).eqTrans (linear_monic _ _ _ pos.wk Prf.hyp0)
  simpa only [Fm.subst_eq,subst_entry,subst_reconstruct,ConciseIPRA.PTm.subst_zero,
    GaussianRationalSyntheticDivision.subst_qone,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all


/-- Actual suffix polynomials retain the original forward root indices. -/
theorem suffix_step (S N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    suffix S N j ≐ linear (suffix S N (succ j)) (entry S j) (remaining N j) := by
  have rootIndex : Γ ⊢[PRAAx] monus N (succ (monus N (succ j))) ≐ j :=
    (congrMonus (AnalyticNumberTheory.Totatives.split_lt hj) (.eqRefl _)).eqTrans (add_monus' _ _)
  exact ((reconstruct_index_congr S N (remaining_step N j hj)).eqTrans
    (reconstruct_succ S N (remaining N (succ j)))).eqTrans
      (linear_congr (.eqRefl _) (entry_congr (.eqRefl _) rootIndex)
        ((reconstruct_length S N (remaining N (succ j))).eqTrans (remaining_step N j hj).eqSymm))

theorem suffix_final (S N : PTm n) : Γ ⊢[PRAAx] suffix S N N ≐ singleton qone :=
  (reconstruct_index_congr S N (monus_self N)).eqTrans (reconstruct_zero S N)

theorem suffix_length (S N j : PTm n) : Γ ⊢[PRAAx] length (suffix S N j) ≐ succ (remaining N j) :=
  reconstruct_length S N (remaining N j)

theorem suffix_canonical (S N j : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (suffix S N j) :=
  reconstruct_canonical S N (remaining N j)

theorem suffix_monic (S N j : PTm n) : Γ ⊢[PRAAx] entry (suffix S N j) zero ≐ qone :=
  reconstruct_monic S N (remaining N j)

def factorData (S N y : PTm n) : PTm n := pairT S (pairT N y)
def factorStep : PTm 3 := qmul
  (qsub (sndT (sndT (var 2)))
    (entry (fstT (var 2)) (monus (fstT (sndT (var 2))) (succ (var 0))))) (var 1)
def factorsF : PR 2 := rec2 qone factorStep
def factors (S N y k : PTm n) : PTm n := ap2 factorsF k (factorData S N y)
def product (S N y : PTm n) : PTm n := factors S N y N

@[simp] theorem subst_factorData {m : ℕ} (σ : Fin n → PTm m) (S N y : PTm n) :
    Syn.subst σ (factorData S N y) = factorData (Syn.subst σ S) (Syn.subst σ N) (Syn.subst σ y) := by
  simp only [factorData,subst_pairT]
@[simp] theorem subst_factors {m : ℕ} (σ : Fin n → PTm m) (S N y k : PTm n) :
    Syn.subst σ (factors S N y k) = factors (Syn.subst σ S) (Syn.subst σ N) (Syn.subst σ y) (Syn.subst σ k) := by
  simp only [factors,subst_ap2,subst_factorData]
@[simp] theorem subst_product {m : ℕ} (σ : Fin n → PTm m) (S N y : PTm n) :
    Syn.subst σ (product S N y) = product (Syn.subst σ S) (Syn.subst σ N) (Syn.subst σ y) := by simp only [product,subst_factors]

theorem factors_zero (S N y : PTm n) : Γ ⊢[PRAAx] factors S N y zero ≐ qone := by
  simpa only [factors,factorsF,GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) qone factorStep (factorData S N y)

theorem factors_succ (S N y k : PTm n) : Γ ⊢[PRAAx]
    factors S N y (succ k) ≐ qmul (qsub y (entry S (monus N (succ k)))) (factors S N y k) := by
  have h := rec2_succ (Γ := Γ) qone factorStep k (factorData S N y)
  simp only [factorStep,GaussianRationalHorner.subst_qmul,GaussianRationalMetric.subst_qsub,
    subst_entry,subst_fstT,subst_sndT,PTm.subst_monus,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h
  have Sfield : Γ ⊢[PRAAx] fstT (factorData S N y) ≐ S := fst_pair _ _
  have Nfield : Γ ⊢[PRAAx] fstT (sndT (factorData S N y)) ≐ N := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have yfield : Γ ⊢[PRAAx] sndT (sndT (factorData S N y)) ≐ y := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  exact h.eqTrans (qmul_congr (qsub_congr yfield (entry_congr Sfield (congrMonus Nfield (.eqRefl _)))) (.eqRefl _))

theorem evaluate_congr {C D y z : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hy : Γ ⊢[PRAAx] y ≐ z) :
    Γ ⊢[PRAAx] evaluate C y ≐ evaluate D z :=
  congrAp3 GaussianRationalHorner.hornerF (congrFst hC) hC hy

theorem singleton_evaluation (y : PTm n) : Γ ⊢[PRAAx] evaluate (singleton qone) y ≐ qone := by
  have count : Γ ⊢[PRAAx] horner (singleton qone) y (length (singleton qone)) ≐ horner (singleton qone) y (succ zero) :=
    congrAp3 GaussianRationalHorner.hornerF (singleton_length _) (.eqRefl _) (.eqRefl _)
  exact count.eqTrans ((GaussianRationalHorner.horner_succ _ _ _).eqTrans
    ((qadd_congr ((qmul_congr (GaussianRationalHorner.horner_zero _ _) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_left y)) (singleton_entry _)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add qone qone_canonical)))

/-- The independently computed scalar factor fold is the actual Horner
value of the produced coefficient list, uniformly in the runtime counter. -/
theorem reconstruction_evaluation (S N y k : PTm n) : Γ ⊢[PRAAx]
    evaluate (reconstruct S N k) y ≐ factors S N y k := by
  have all : Γ ⊢[PRAAx] .all (evaluate (reconstruct (Syn.shift S) (Syn.shift N) (var 0)) (Syn.shift y) ≐
      factors (Syn.shift S) (Syn.shift N) (Syn.shift y) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,GaussianRationalHorner.subst_evaluate,subst_reconstruct,subst_factors,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact ((evaluate_congr (reconstruct_zero S N) (.eqRefl _)).eqTrans (singleton_evaluation y)).eqTrans (factors_zero S N y).eqSymm
    · simp only [Fm.subst_eq,GaussianRationalHorner.subst_evaluate,subst_reconstruct,subst_factors,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (evaluate_congr (reconstruct_succ _ _ _) (.eqRefl _)).eqTrans
        ((GaussianRationalLinearProduct.linear_evaluation _ _ _ _ (.eqRefl _) (reconstruct_canonical _ _ _)).eqTrans
          ((qmul_congr (.eqRefl _) Prf.hyp0).eqTrans (factors_succ _ _ _ _).eqSymm))
  simpa only [Fm.subst_eq,GaussianRationalHorner.subst_evaluate,subst_reconstruct,subst_factors,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all

/-- The final scalar program has normal forward factor order: factor j
multiplies the already computed tail of factors j+1 through N-1. -/
theorem factors_suffix_step (S N y j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    factors S N y (remaining N j) ≐
      qmul (qsub y (entry S j)) (factors S N y (remaining N (succ j))) := by
  have rootIndex : Γ ⊢[PRAAx] monus N (succ (monus N (succ j))) ≐ j :=
    (congrMonus (AnalyticNumberTheory.Totatives.split_lt hj) (.eqRefl _)).eqTrans (add_monus' _ _)
  exact ((congrAp2 factorsF (remaining_step N j hj) (.eqRefl _)).eqTrans (factors_succ _ _ _ _)).eqTrans
    (qmul_congr (qsub_congr (.eqRefl _) (entry_congr (.eqRefl _) rootIndex)) (.eqRefl _))

theorem product_evaluation (S N y : PTm n) : Γ ⊢[PRAAx] evaluate (reconstruct S N N) y ≐ product S N y :=
  reconstruction_evaluation S N y N


theorem suffix_zero (S N : PTm n) : Γ ⊢[PRAAx] suffix S N zero ≐ reconstruct S N N :=
  reconstruct_index_congr S N (monus_zero N)

theorem suffix_evaluation (S N y j : PTm n) : Γ ⊢[PRAAx]
    evaluate (suffix S N j) y ≐ factors S N y (remaining N j) :=
  reconstruction_evaluation S N y (remaining N j)

/-- The generic producer returns the actual runtime coefficient list. -/
def reconstructionProgramF : PR 3 := PTm.toPR (reconstruct (var 0) (var 1) (var 2))
def productProgramF : PR 3 := PTm.toPR
  (pairT (reconstruct (var 0) (var 1) (var 1)) (product (var 0) (var 1) (var 2)))

theorem reconstruction_program_at (S N k : PTm n) : Γ ⊢[PRAAx]
    ap3 reconstructionProgramF S N k ≐ reconstruct S N k := by
  simpa only [reconstructionProgramF,ap3,subst_reconstruct,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (reconstruct (var 0) (var 1) (var 2) : PTm 3) ![S,N,k]

theorem product_program_at (S N y : PTm n) : Γ ⊢[PRAAx]
    ap3 productProgramF S N y ≐ pairT (reconstruct S N N) (product S N y) := by
  simpa only [productProgramF,ap3,subst_pairT,subst_reconstruct,subst_product,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ)
      (pairT (reconstruct (var 0) (var 1) (var 1)) (product (var 0) (var 1) (var 2)) : PTm 3) ![S,N,y]

theorem product_program_metadata (S N y : PTm n) : Γ ⊢[PRAAx]
    (length (fstT (ap3 productProgramF S N y)) ≐ succ N) ⋏
      (evaluate (fstT (ap3 productProgramF S N y)) y ≐ sndT (ap3 productProgramF S N y)) := by
  have coeffs : Γ ⊢[PRAAx] fstT (ap3 productProgramF S N y) ≐ reconstruct S N N :=
    (congrFst (product_program_at S N y)).eqTrans (fst_pair _ _)
  have value : Γ ⊢[PRAAx] sndT (ap3 productProgramF S N y) ≐ product S N y :=
    (congrSnd (product_program_at S N y)).eqTrans (snd_pair _ _)
  exact .andI ((congrFst coeffs).eqTrans (reconstruct_length S N N))
    (((evaluate_congr coeffs (.eqRefl _)).eqTrans (product_evaluation S N y)).eqTrans value.eqSymm)

theorem reconstruction_structure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (reconstruct (var 0) (var 1) (var 2)) ≐ succ (var 2)) ⋏
      (canonicalCoefficients (reconstruct (var 0) (var 1) (var 2)) ⋏
        (entry (reconstruct (var 0) (var 1) (var 2)) zero ≐ qone))) :=
  closeUniv 3 (.andI (reconstruct_length _ _ _) (.andI (reconstruct_canonical _ _ _) (reconstruct_monic _ _ _)))

theorem reconstruction_suffix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ suffix (var 0) (var 1) (var 2) ≐
      linear (suffix (var 0) (var 1) (succ (var 2))) (entry (var 0) (var 2)) (remaining (var 1) (var 2))) :=
  closeUniv 3 (.impI (suffix_step _ _ _ Prf.hyp0))

theorem reconstruction_terminal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (suffix (var 0) (var 1) (var 1) ≐ singleton qone) := closeUniv 2 (suffix_final _ _)

theorem reconstruction_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (evaluate (reconstruct (var 0) (var 1) (var 3)) (var 2) ≐ factors (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (reconstruction_evaluation _ _ _ _)

theorem reconstruction_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (reconstruct (var 0) (var 1) (var 1)) (var 2) ≐ product (var 0) (var 1) (var 2)) :=
  closeUniv 3 (product_evaluation _ _ _)

theorem reconstruction_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 reconstructionProgramF (var 0) (var 1) (var 2) ≐ reconstruct (var 0) (var 1) (var 2)) :=
  closeUniv 3 (reconstruction_program_at _ _ _)

theorem reconstruction_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (fstT (ap3 productProgramF (var 0) (var 1) (var 2))) ≐ succ (var 1)) ⋏
      (evaluate (fstT (ap3 productProgramF (var 0) (var 1) (var 2))) (var 2) ≐
        sndT (ap3 productProgramF (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (product_program_metadata _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalReconstruction
