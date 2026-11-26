import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalFiniteSum
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalLinearProduct
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual zero buffers, padding and addition for rational polynomials

The stored coefficient order is descending. Every buffer length and prefix
is numerical. Generated zero padding and pointwise addition have their actual
Horner values proved by guarded quantifier-free induction. Original entries
may be raw codes: only normalized arithmetic outputs are identified.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul canonical horner hornerF evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qadd_congr qmul_congr qzero_canonical qmul_zero_left qzero_add)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct
  (padded padded_inside padded_outside horner_ext)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zerosBody : PTm 2 := qzero
def zeros (L : PTm n) : PTm n := sequence zerosBody L zero
def appendBody : PTm 2 := padded (var 1) (length (var 1)) (var 0)
def appendZero (C : PTm n) : PTm n := sequence appendBody (succ (length C)) C
def padCoefficient (C t i : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg (monus t i)) (entry C (monus i t)) qzero
def padData (C t : PTm n) : PTm n := pairT C t
def padBody : PTm 2 := padCoefficient (fstT (var 1)) (sndT (var 1)) (var 0)
def leftPad (C t : PTm n) : PTm n := sequence padBody (t+length C) (padData C t)
def addBody : PTm 2 := qadd (entry (fstT (var 1)) (var 0)) (entry (sndT (var 1)) (var 0))
def added (C D L : PTm n) : PTm n := sequence addBody L (pairT C D)

@[simp] theorem subst_zeros {m : ℕ} (σ : Fin n → PTm m) (L : PTm n) :
    Syn.subst σ (zeros L) = zeros (Syn.subst σ L) := by simp [zeros]
@[simp] theorem subst_appendZero {m : ℕ} (σ : Fin n → PTm m) (C : PTm n) :
    Syn.subst σ (appendZero C) = appendZero (Syn.subst σ C) := by simp [appendZero]
@[simp] theorem subst_padCoefficient {m : ℕ} (σ : Fin n → PTm m) (C t i : PTm n) :
    Syn.subst σ (padCoefficient C t i) = padCoefficient (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ i) := by
  simp [padCoefficient,Signum.sg]
@[simp] theorem subst_padData {m : ℕ} (σ : Fin n → PTm m) (C t : PTm n) :
    Syn.subst σ (padData C t) = padData (Syn.subst σ C) (Syn.subst σ t) := by simp [padData]
@[simp] theorem subst_leftPad {m : ℕ} (σ : Fin n → PTm m) (C t : PTm n) :
    Syn.subst σ (leftPad C t) = leftPad (Syn.subst σ C) (Syn.subst σ t) := by simp [leftPad]
@[simp] theorem subst_added {m : ℕ} (σ : Fin n → PTm m) (C D L : PTm n) :
    Syn.subst σ (added C D L) = added (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ L) := by simp [added]

theorem zeros_length (L : PTm n) : Γ ⊢[PRAAx] length (zeros L) ≐ L := sequence_length _ _ _
theorem zeros_lookup (L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) :
    Γ ⊢[PRAAx] entry (zeros L) i ≐ qzero := by
  simpa [zeros,zerosBody,inst2] using sequence_decode zerosBody (x := (zero : PTm n)) hi

theorem append_body_at (C i : PTm n) : Γ ⊢[PRAAx]
    inst2 appendBody i C ≐ padded C (length C) i := by
  simpa [appendBody,inst2] using Prf.eqRefl (Ax := PRAAx) (Γ := Γ) (padded C (length C) i)

theorem append_length (C : PTm n) : Γ ⊢[PRAAx] length (appendZero C) ≐ succ (length C) := sequence_length _ _ _
theorem append_lookup (C i : PTm n) (hi : Γ ⊢[PRAAx] le i (length C)) : Γ ⊢[PRAAx]
    entry (appendZero C) i ≐ padded C (length C) i :=
  (sequence_decode appendBody ((succ_monus_succ _ _).eqTrans hi)).eqTrans (append_body_at C i)

theorem pad_coefficient_congr {C D t u i j : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D)
    (ht : Γ ⊢[PRAAx] t ≐ u) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx]
    padCoefficient C t i ≐ padCoefficient D u j := by
  ipra_congr (padCoefficient (var 0) (var 1) (var 2) : PTm 3) with [hC, ht, hi]

theorem pad_body_at (C t i : PTm n) : Γ ⊢[PRAAx]
    inst2 padBody i (padData C t) ≐ padCoefficient C t i := by
  simp only [padBody,inst2,subst_padCoefficient,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact pad_coefficient_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)

theorem pad_coefficient_before (C t i : PTm n) (hi : Γ ⊢[PRAAx] lt i t) : Γ ⊢[PRAAx]
    padCoefficient C t i ≐ qzero :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hi)

theorem pad_coefficient_after (C t i : PTm n) (hi : Γ ⊢[PRAAx] le t i) : Γ ⊢[PRAAx]
    padCoefficient C t i ≐ entry C (monus i t) :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hi)

theorem pad_length (C t : PTm n) : Γ ⊢[PRAAx] length (leftPad C t) ≐ t+length C := sequence_length _ _ _
theorem pad_lookup (C t i : PTm n) (hi : Γ ⊢[PRAAx] lt i (t+length C)) : Γ ⊢[PRAAx]
    entry (leftPad C t) i ≐ padCoefficient C t i :=
  (sequence_decode padBody hi).eqTrans (pad_body_at C t i)

theorem pad_leading (C t i : PTm n) (hi : Γ ⊢[PRAAx] lt i t) : Γ ⊢[PRAAx]
    entry (leftPad C t) i ≐ qzero :=
  (pad_lookup C t i (le_trans hi (le_add_right _ _))).eqTrans (pad_coefficient_before C t i hi)

theorem pad_tail (C t i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx]
    entry (leftPad C t) (t+i) ≐ entry C i :=
  (pad_lookup C t (t+i) (le_congr (by ipra_ring : Γ ⊢[PRAAx] t+succ i ≐ succ (t+i)) (.eqRefl _) (add_le_add₂ (le_refl t) hi))).eqTrans
    ((pad_coefficient_after C t (t+i) (le_add_right _ _)).eqTrans
      (entry_congr (.eqRefl _) ((congrMonus (add_comm t i) (.eqRefl t)).eqTrans (add_monus i t))))

theorem added_length (C D L : PTm n) : Γ ⊢[PRAAx] length (added C D L) ≐ L := sequence_length _ _ _
theorem add_body_at (C D i : PTm n) : Γ ⊢[PRAAx]
    inst2 addBody i (pairT C D) ≐ qadd (entry C i) (entry D i) := by
  simp only [addBody,inst2,GaussianRationalHorner.subst_qadd,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qadd_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (entry_congr (snd_pair _ _) (.eqRefl _))
theorem added_lookup (C D L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) : Γ ⊢[PRAAx]
    entry (added C D L) i ≐ qadd (entry C i) (entry D i) :=
  (sequence_decode addBody hi).eqTrans (add_body_at C D i)

def zeroLaw (L z r : PTm n) : Fm PTm n := le r L ⟶ horner (zeros L) z r ≐ qzero
@[simp] theorem subst_zeroLaw {m : ℕ} (σ : Fin n → PTm m) (L z r : PTm n) :
    (zeroLaw L z r).subst σ = zeroLaw (Syn.subst σ L) (Syn.subst σ z) (Syn.subst σ r) := by simp [zeroLaw]

theorem zeros_prefix (L z r : PTm n) (hr : Γ ⊢[PRAAx] le r L) : Γ ⊢[PRAAx]
    horner (zeros L) z r ≐ qzero := by
  have all : Γ ⊢[PRAAx] .all (zeroLaw (Syn.shift L) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_zeroLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (GaussianRationalHorner.horner_zero _ _)
    · simp only [subst_zeroLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift L) :: zeroLaw (Syn.shift L) (Syn.shift z) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] horner (zeros (Syn.shift L)) (Syn.shift z) (var 0) ≐ qzero :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
        ((qadd_congr ((qmul_congr ih (.eqRefl _)).eqTrans (qmul_zero_left _))
          (zeros_lookup _ _ Prf.hyp0)).eqTrans (qzero_add _ qzero_canonical))
  have rule : Γ ⊢[PRAAx] zeroLaw L z r := by
    simpa only [subst_zeroLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem zeros_evaluation (L z : PTm n) : Γ ⊢[PRAAx] evaluate (zeros L) z ≐ qzero :=
  (congrAp3 hornerF (zeros_length L) (.eqRefl _) (.eqRefl _)).eqTrans (zeros_prefix L z L (le_refl _))

theorem append_prefix (C z r : PTm n) (hr : Γ ⊢[PRAAx] le r (length C)) : Γ ⊢[PRAAx]
    horner (appendZero C) z r ≐ horner C z r := by
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (length C)) ⟶
      entry (Syn.shift (appendZero C)) (var 0) ≐ entry (Syn.shift C) (var 0)) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_appendZero,subst_length] using
      (append_lookup (Syn.shift C) (var 0) (le_of_lt Prf.hyp0)).eqTrans
        (padded_inside _ _ _ Prf.hyp0)
  exact horner_ext _ _ _ _ _ entries hr

theorem append_evaluation (C z : PTm n) : Γ ⊢[PRAAx]
    evaluate (appendZero C) z ≐ qmul (evaluate C z) z :=
  (congrAp3 hornerF (append_length C) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalHorner.horner_succ _ _ _).eqTrans
      ((qadd_congr (qmul_congr (append_prefix C z (length C) (le_refl _)) (.eqRefl _))
        ((append_lookup C (length C) (le_refl _)).eqTrans (padded_outside C _ _ (le_refl _)))).eqTrans
          (GaussianRationalLinearProduct.qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _))))

def leadingLaw (C t z r : PTm n) : Fm PTm n := le r t ⟶ horner (leftPad C t) z r ≐ qzero
def tailLaw (C t z r : PTm n) : Fm PTm n := le r (length C) ⟶
  horner (leftPad C t) z (t+r) ≐ horner C z r
@[simp] theorem subst_leadingLaw {m : ℕ} (σ : Fin n → PTm m) (C t z r : PTm n) :
    (leadingLaw C t z r).subst σ = leadingLaw (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ r) := by simp [leadingLaw]
@[simp] theorem subst_tailLaw {m : ℕ} (σ : Fin n → PTm m) (C t z r : PTm n) :
    (tailLaw C t z r).subst σ = tailLaw (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ r) := by simp [tailLaw]

theorem pad_leading_prefix (C t z r : PTm n) (hr : Γ ⊢[PRAAx] le r t) : Γ ⊢[PRAAx]
    horner (leftPad C t) z r ≐ qzero := by
  have all : Γ ⊢[PRAAx] .all (leadingLaw (Syn.shift C) (Syn.shift t) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_leadingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (GaussianRationalHorner.horner_zero _ _)
    · simp only [subst_leadingLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift t) :: leadingLaw (Syn.shift C) (Syn.shift t) (Syn.shift z) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] horner (leftPad (Syn.shift C) (Syn.shift t)) (Syn.shift z) (var 0) ≐ qzero :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
        ((qadd_congr ((qmul_congr ih (.eqRefl _)).eqTrans (qmul_zero_left _))
          (pad_leading _ _ _ Prf.hyp0)).eqTrans (qzero_add _ qzero_canonical))
  have rule : Γ ⊢[PRAAx] leadingLaw C t z r := by
    simpa only [subst_leadingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem pad_tail_prefix (C t z r : PTm n) (hr : Γ ⊢[PRAAx] le r (length C)) : Γ ⊢[PRAAx]
    horner (leftPad C t) z (t+r) ≐ horner C z r := by
  have all : Γ ⊢[PRAAx] .all (tailLaw (Syn.shift C) (Syn.shift t) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_tailLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((congrAp3 hornerF (add_zero _) (.eqRefl _) (.eqRefl _)).eqTrans
        ((pad_leading_prefix C t z t (le_refl _)).eqTrans (GaussianRationalHorner.horner_zero C z).eqSymm)).wk
    · simp only [subst_tailLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (length (Syn.shift C)) :: tailLaw (Syn.shift C) (Syn.shift t) (Syn.shift z) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] horner (leftPad (Syn.shift C) (Syn.shift t)) (Syn.shift z) (Syn.shift t+var 0) ≐ horner (Syn.shift C) (Syn.shift z) (var 0) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact (congrAp3 hornerF (by ipra_ring : Δ ⊢[PRAAx] Syn.shift t+succ (var 0) ≐ succ (Syn.shift t+var 0)) (.eqRefl _) (.eqRefl _)).eqTrans
        ((GaussianRationalHorner.horner_succ _ _ _).eqTrans
          ((qadd_congr (qmul_congr ih (.eqRefl _)) (pad_tail _ _ _ Prf.hyp0)).eqTrans
            (GaussianRationalHorner.horner_succ _ _ _).eqSymm))
  have rule : Γ ⊢[PRAAx] tailLaw C t z r := by
    simpa only [subst_tailLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem pad_evaluation (C t z : PTm n) : Γ ⊢[PRAAx]
    evaluate (leftPad C t) z ≐ evaluate C z :=
  (congrAp3 hornerF (pad_length C t) (.eqRefl _) (.eqRefl _)).eqTrans
    (pad_tail_prefix C t z (length C) (le_refl _))

theorem distribute_right (a b z : PTm n) : Γ ⊢[PRAAx]
    qmul (qadd a b) z ≐ qadd (qmul a z) (qmul b z) :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _)
        (GaussianRationalPowerAlgebra.qmul_commutative _ _)))

def addLaw (C D L z r : PTm n) : Fm PTm n := le r L ⟶
  horner (added C D L) z r ≐ qadd (horner C z r) (horner D z r)
@[simp] theorem subst_addLaw {m : ℕ} (σ : Fin n → PTm m) (C D L z r : PTm n) :
    (addLaw C D L z r).subst σ = addLaw (Syn.subst σ C) (Syn.subst σ D)
      (Syn.subst σ L) (Syn.subst σ z) (Syn.subst σ r) := by simp [addLaw]

theorem added_prefix (C D L z r : PTm n) (hr : Γ ⊢[PRAAx] le r L) : Γ ⊢[PRAAx]
    horner (added C D L) z r ≐ qadd (horner C z r) (horner D z r) := by
  have all : Γ ⊢[PRAAx] .all (addLaw (Syn.shift C) (Syn.shift D) (Syn.shift L) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_addLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((GaussianRationalHorner.horner_zero _ _).eqTrans
        ((qzero_add qzero qzero_canonical).eqSymm.eqTrans
          (qadd_congr (GaussianRationalHorner.horner_zero C z).eqSymm
            (GaussianRationalHorner.horner_zero D z).eqSymm)))
    · simp only [subst_addLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift L) :: addLaw (Syn.shift C) (Syn.shift D) (Syn.shift L) (Syn.shift z) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] horner (added (Syn.shift C) (Syn.shift D) (Syn.shift L)) (Syn.shift z) (var 0) ≐
          qadd (horner (Syn.shift C) (Syn.shift z) (var 0)) (horner (Syn.shift D) (Syn.shift z) (var 0)) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
        ((qadd_congr ((qmul_congr ih (.eqRefl _)).eqTrans (distribute_right _ _ _))
          (added_lookup _ _ _ _ Prf.hyp0)).eqTrans
            (((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm.eqTrans
              (GaussianRationalSumAlgebra.shuffle_four _ _ _ _)).eqTrans
              (qadd_congr (GaussianRationalHorner.horner_succ _ _ _).eqSymm
                (GaussianRationalHorner.horner_succ _ _ _).eqSymm)))
  have rule : Γ ⊢[PRAAx] addLaw C D L z r := by
    simpa only [subst_addLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem added_evaluation (C D L z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ L)
    (hD : Γ ⊢[PRAAx] length D ≐ L) : Γ ⊢[PRAAx]
    evaluate (added C D L) z ≐ qadd (evaluate C z) (evaluate D z) :=
  (congrAp3 hornerF (added_length C D L) (.eqRefl _) (.eqRefl _)).eqTrans
    ((added_prefix C D L z L (le_refl _)).eqTrans
      (qadd_congr (congrAp3 hornerF hC.eqSymm (.eqRefl _) (.eqRefl _))
        (congrAp3 hornerF hD.eqSymm (.eqRefl _) (.eqRefl _))))

/-! One fixed PR3 returns all four literal buffer programs. -/
def output (C D L : PTm n) : PTm n :=
  pairT (zeros L) (pairT (appendZero C) (pairT (leftPad C L) (added C D L)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C D L : PTm n) : PTm n := ap3 outputF C D L

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C D L : PTm n) :
    Syn.subst σ (output C D L) = output (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ L) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C D L : PTm n) :
    Syn.subst σ (run C D L) = run (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ L) := by simp [run]

theorem program_at (C D L : PTm n) : Γ ⊢[PRAAx] run C D L ≐ output C D L := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,D,L]
theorem returned_zeros (C D L : PTm n) : Γ ⊢[PRAAx] fstT (run C D L) ≐ zeros L :=
  (congrFst (program_at C D L)).eqTrans (fst_pair _ _)
theorem returned_append (C D L : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C D L)) ≐ appendZero C :=
  (congrFst ((congrSnd (program_at C D L)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_pad (C D L : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C D L))) ≐ leftPad C L :=
  (congrFst ((congrSnd ((congrSnd (program_at C D L)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_add (C D L : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run C D L))) ≐ added C D L :=
  (congrSnd ((congrSnd ((congrSnd (program_at C D L)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_zero_buffer_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (evaluate (zeros (var 0)) (var 1) ≐ qzero) := closeUniv 2 (zeros_evaluation _ _)
theorem actual_append_zero_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (evaluate (appendZero (var 0)) (var 1) ≐ qmul (evaluate (var 0) (var 1)) (var 1)) :=
  closeUniv 2 (append_evaluation _ _)
theorem actual_left_pad_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (leftPad (var 0) (var 1)) (var 2) ≐ evaluate (var 0) (var 2)) :=
  closeUniv 3 (pad_evaluation _ _ _)
theorem actual_polynomial_add_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ var 2 ⟶ length (var 1) ≐ var 2 ⟶
      evaluate (added (var 0) (var 1) (var 2)) (var 3) ≐
        qadd (evaluate (var 0) (var 3)) (evaluate (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (added_evaluation _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_polynomial_buffer_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (run (var 0) (var 1) (var 2)) ≐ zeros (var 2)) ⋏
      ((fstT (sndT (run (var 0) (var 1) (var 2))) ≐ appendZero (var 0)) ⋏
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ leftPad (var 0) (var 2)) ⋏
          (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ added (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (returned_zeros _ _ _) (.andI (returned_append _ _ _)
    (.andI (returned_pad _ _ _) (returned_add _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
