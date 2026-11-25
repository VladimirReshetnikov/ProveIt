import IPRADerivations.Analysis.GaussianRationalL1Algebra
import IPRADerivations.Analysis.RationalSumAdditivity
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual finite Gaussian-rational coefficient norms

The coefficient norm is the normalized rational sum of the actual component
L1 norms. Addition and subtraction construct real coefficient sequences of
runtime length N. Their coefficient-norm triangle estimates use the proved
scalar estimates and the actual independently denominated finite sum. These
are components of finite-demand approximate factorization; polynomial
convolution and the deflation/telescoping identity are separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCoefficientL1

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qadd)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def normBody : PTm 2 := qL1 (entry (var 1) (var 0))
def prefixNorm (C N : PTm n) : PTm n := RationalFiniteSum.sum normBody N C
def coefficientNorm (C : PTm n) : PTm n := prefixNorm C (length C)

@[simp] theorem subst_prefixNorm {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (prefixNorm C N) = prefixNorm (Syn.subst σ C) (Syn.subst σ N) := by simp [prefixNorm]
@[simp] theorem subst_coefficientNorm {m : ℕ} (σ : Fin n → PTm m) (C : PTm n) :
    Syn.subst σ (coefficientNorm C) = coefficientNorm (Syn.subst σ C) := by simp [coefficientNorm]

theorem norm_body_at (C i : PTm n) : RationalFiniteSum.term normBody i C = qL1 (entry C i) := by
  simp only [normBody,RationalFiniteSum.term,inst2,GaussianRationalL1.subst_qL1,subst_entry,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem qL1_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] qL1 q ≐ qL1 r := by
  ipra_congr (qL1 (var 0) : PTm 1) with [h]

theorem prefix_zero (C : PTm n) : Γ ⊢[PRAAx]
    prefixNorm C zero ≐ RationalIntegerNormalization.integerCode (ZT.natLit 0) :=
  RationalFiniteSum.sum_zero _ _
theorem prefix_succ (C N : PTm n) : Γ ⊢[PRAAx]
    prefixNorm C (succ N) ≐ RationalArithmetic.add (prefixNorm C N) (qL1 (entry C N)) := by
  simpa only [prefixNorm,norm_body_at] using RationalFiniteSum.sum_succ (Γ := Γ) normBody N C
theorem norm_guard (C : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (coefficientNorm C) :=
  RationalFiniteSum.sum_well_formed _ _ _

def addF : PR 2 := PTm.toPR (qadd (var 0) (var 1))
def subF : PR 2 := PTm.toPR (qsub (var 0) (var 1))
def zipBody (op : PR 2) : PTm 2 := ap2 op
  (entry (fstT (var 1)) (var 0)) (entry (sndT (var 1)) (var 0))
def zip (op : PR 2) (C D N : PTm n) : PTm n := sequence (zipBody op) N (pairT C D)
def addCoefficients (C D N : PTm n) : PTm n := zip addF C D N
def subCoefficients (C D N : PTm n) : PTm n := zip subF C D N

@[simp] theorem subst_zip {m : ℕ} (σ : Fin n → PTm m) (op : PR 2) (C D N : PTm n) :
    Syn.subst σ (zip op C D N) = zip op (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ N) := by simp [zip]
@[simp] theorem subst_addCoefficients {m : ℕ} (σ : Fin n → PTm m) (C D N : PTm n) :
    Syn.subst σ (addCoefficients C D N) = addCoefficients (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ N) := by simp [addCoefficients]
@[simp] theorem subst_subCoefficients {m : ℕ} (σ : Fin n → PTm m) (C D N : PTm n) :
    Syn.subst σ (subCoefficients C D N) = subCoefficients (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ N) := by simp [subCoefficients]

theorem add_at (q r : PTm n) : Γ ⊢[PRAAx] ap2 addF q r ≐ qadd q r := by
  simpa [addF,ap2] using toPR_eq (Γ := Γ) (qadd (var 0) (var 1) : PTm 2) ![q,r]
theorem sub_at (q r : PTm n) : Γ ⊢[PRAAx] ap2 subF q r ≐ qsub q r := by
  simpa [subF,ap2] using toPR_eq (Γ := Γ) (qsub (var 0) (var 1) : PTm 2) ![q,r]

theorem zip_body_at (op : PR 2) (C D i : PTm n) : Γ ⊢[PRAAx]
    inst2 (zipBody op) i (pairT C D) ≐ ap2 op (entry C i) (entry D i) := by
  simp only [zipBody,inst2,subst_ap2,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply congrAp2
  · exact congrFst (congrAp2 _ (congrMonus (congrFst (fst_pair C D)) (.eqRefl _)) (congrSnd (fst_pair C D)))
  · exact congrFst (congrAp2 _ (congrMonus (congrFst (snd_pair C D)) (.eqRefl _)) (congrSnd (snd_pair C D)))

theorem zip_length (op : PR 2) (C D N : PTm n) : Γ ⊢[PRAAx] length (zip op C D N) ≐ N := sequence_length _ _ _
theorem zip_lookup (op : PR 2) (C D N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (zip op C D N) i ≐ ap2 op (entry C i) (entry D i) :=
  (sequence_decode _ hi).eqTrans (zip_body_at op C D i)

theorem add_lookup (C D N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (addCoefficients C D N) i ≐ qadd (entry C i) (entry D i) :=
  (zip_lookup addF C D N i hi).eqTrans (add_at _ _)
theorem sub_lookup (C D N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (subCoefficients C D N) i ≐ qsub (entry C i) (entry D i) :=
  (zip_lookup subF C D N i hi).eqTrans (sub_at _ _)

theorem prefix_monotone (C D N : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      rationalLE (qL1 (entry (Syn.shift C) (var 0))) (qL1 (entry (Syn.shift D) (var 0))))) :
    Γ ⊢[PRAAx] rationalLE (prefixNorm C N) (prefixNorm D N) := by
  apply RationalFiniteSum.sum_monotone
  simpa only [RationalFiniteSum.termwiseLE,norm_body_at] using h

theorem prefix_add (C D N : PTm n) : Γ ⊢[PRAAx]
    rationalLE (prefixNorm (addCoefficients C D N) N) (RationalArithmetic.add (prefixNorm C N) (prefixNorm D N)) := by
  have h : Γ ⊢[PRAAx] RationalFiniteSum.termwiseLE normBody
      (RationalSumAdditivity.addedBody normBody normBody) N (addCoefficients C D N) (pairT C D) := by
    refine .allI (.impI ?_)
    have hi := Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift N))
    have a := qL1_congr (add_lookup (Syn.shift C) (Syn.shift D) (Syn.shift N) (var 0) hi)
    have b := RationalSumAdditivity.added_term (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
      normBody normBody (var 0) (Syn.shift C) (Syn.shift D)
    simp only [norm_body_at] at b
    simpa only [norm_body_at,Syn.shift,subst_addCoefficients,subst_pairT] using
      RationalArgmin.rationalLE_congr a.eqSymm b.eqSymm (GaussianRationalL1Algebra.qL1_add _ _)
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (RationalSumAdditivity.sum_additive _ _ _ _ _)
    (RationalFiniteSum.sum_monotone _ _ _ _ _ h)

theorem prefix_sub (C D N : PTm n) : Γ ⊢[PRAAx]
    rationalLE (prefixNorm (subCoefficients C D N) N) (RationalArithmetic.add (prefixNorm C N) (prefixNorm D N)) := by
  have h : Γ ⊢[PRAAx] RationalFiniteSum.termwiseLE normBody
      (RationalSumAdditivity.addedBody normBody normBody) N (subCoefficients C D N) (pairT C D) := by
    refine .allI (.impI ?_)
    have hi := Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift N))
    have a := qL1_congr (sub_lookup (Syn.shift C) (Syn.shift D) (Syn.shift N) (var 0) hi)
    have b := RationalSumAdditivity.added_term (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
      normBody normBody (var 0) (Syn.shift C) (Syn.shift D)
    simp only [norm_body_at] at b
    simpa only [norm_body_at,Syn.shift,subst_subCoefficients,subst_pairT] using
      RationalArgmin.rationalLE_congr a.eqSymm b.eqSymm (GaussianRationalL1Algebra.qL1_sub _ _)
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (RationalSumAdditivity.sum_additive _ _ _ _ _)
    (RationalFiniteSum.sum_monotone _ _ _ _ _ h)

theorem coefficient_add (C D N : PTm n) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (addCoefficients C D N)) (RationalArithmetic.add (prefixNorm C N) (prefixNorm D N)) := by
  have e := congrAp2 (Γ := Γ) (RationalFiniteSum.sumCodeF normBody) (zip_length addF C D N) (.eqRefl (addCoefficients C D N))
  have lengthEq : Γ ⊢[PRAAx] coefficientNorm (addCoefficients C D N) ≐ prefixNorm (addCoefficients C D N) N :=
    (RationalFiniteSum.sum_at _ _ _).eqSymm.eqTrans (e.eqTrans (RationalFiniteSum.sum_at _ _ _))
  exact RationalArgmin.rationalLE_congr lengthEq.eqSymm (.eqRefl _) (prefix_add C D N)

theorem coefficient_sub (C D N : PTm n) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (subCoefficients C D N)) (RationalArithmetic.add (prefixNorm C N) (prefixNorm D N)) := by
  have e := congrAp2 (Γ := Γ) (RationalFiniteSum.sumCodeF normBody) (zip_length subF C D N) (.eqRefl (subCoefficients C D N))
  have lengthEq : Γ ⊢[PRAAx] coefficientNorm (subCoefficients C D N) ≐ prefixNorm (subCoefficients C D N) N :=
    (RationalFiniteSum.sum_at _ _ _).eqSymm.eqTrans (e.eqTrans (RationalFiniteSum.sum_at _ _ _))
  exact RationalArgmin.rationalLE_congr lengthEq.eqSymm (.eqRefl _) (prefix_sub C D N)

def output (C D N : PTm n) : PTm n := pairT (addCoefficients C D N)
  (pairT (subCoefficients C D N) (pairT (coefficientNorm C) (coefficientNorm D)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C D N : PTm n) :
    Syn.subst σ (output C D N) = output (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ N) := by simp [output]
theorem output_program (C D N : PTm n) : Γ ⊢[PRAAx] ap3 outputF C D N ≐ output C D N := by
  simpa [outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,D,N]

theorem coefficient_norm_triangle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rationalLE (coefficientNorm (addCoefficients (var 0) (var 1) (var 2)))
        (RationalArithmetic.add (prefixNorm (var 0) (var 2)) (prefixNorm (var 1) (var 2))) ⋏
      rationalLE (coefficientNorm (subCoefficients (var 0) (var 1) (var 2)))
        (RationalArithmetic.add (prefixNorm (var 0) (var 2)) (prefixNorm (var 1) (var 2)))) :=
  closeUniv 3 (.andI (coefficient_add _ _ _) (coefficient_sub _ _ _))
theorem coefficient_norm_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 outputF (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (output_program _ _ _)

end LeanProofs.IPRA.Analysis.GaussianCoefficientL1
