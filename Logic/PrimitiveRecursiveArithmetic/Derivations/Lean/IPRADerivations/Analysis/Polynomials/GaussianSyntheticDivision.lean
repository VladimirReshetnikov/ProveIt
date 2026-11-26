import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootProduct

/-!
# Actual runtime Gaussian-integer synthetic division

Finite-demand source04, the synthetic-division dependency of thm:approx-factor.
Descending quotient coefficient i is the actual Horner prefix of the input
polynomial at z through coefficient i. The quotient is a genuine sequence of
runtime length N and the remainder is actual evaluation at z. Coefficient
reconstruction, evaluation, monicity and degree are derived, with no quotient
or factorization identity supplied. N=0 is allowed for the identities; N≥1
is needed only for a monic quotient, including the constant quotient at N=1.

This module is the signed-pair Gaussian-integer kernel. A canonical rational
frontend is separate, as are the approximate-root and deflation-error bounds.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSyntheticDivision

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im add mul scale zeroCode oneCode)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
open LeanProofs.IPRA.Analysis.GaussianRootProduct
  (horner hornerF horner_zero horner_succ evaluate padded padded_inside padded_outside
    delayed delayed_zero delayed_succ linearCoefficient subst_horner subst_evaluate)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quotientBody : PTm 2 := horner (fstT (var 1)) (sndT (var 1)) (succ (var 0))
def quotient (C z N : PTm n) : PTm n := sequence quotientBody N (pairT C z)
def remainder (C z : PTm n) : PTm n := evaluate C z

@[simp] theorem subst_quotient {m : ℕ} (σ : Fin n → PTm m) (C z N : PTm n) :
    Syn.subst σ (quotient C z N) = quotient (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ N) := by simp [quotient]
@[simp] theorem subst_remainder {m : ℕ} (σ : Fin n → PTm m) (C z : PTm n) :
    Syn.subst σ (remainder C z) = remainder (Syn.subst σ C) (Syn.subst σ z) := by simp [remainder]

theorem quotient_body_at (C z i : PTm n) : Γ ⊢[PRAAx]
    inst2 quotientBody i (pairT C z) ≐ horner C z (succ i) := by
  simp only [quotientBody,inst2,subst_horner,subst_fstT,subst_sndT,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAp3 hornerF (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

theorem quotient_length (C z N : PTm n) : Γ ⊢[PRAAx] length (quotient C z N) ≐ N := sequence_length _ _ _
theorem quotient_lookup (C z N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] entry (quotient C z N) i ≐ horner C z (succ i) :=
  (sequence_decode quotientBody hi).eqTrans (quotient_body_at C z i)

theorem quotient_padded (C z N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] equal (padded (quotient C z N) i) (horner C z (succ i)) :=
  equal_trans (padded_inside _ _ (lt_congr (.eqRefl _) (quotient_length C z N).eqSymm hi))
    (equal_of_code (quotient_lookup C z N i hi))

theorem quotient_delayed_zero (C z N : PTm n) : Γ ⊢[PRAAx]
    equal (delayed (quotient C z N) zero) (horner C z zero) :=
  equal_trans (delayed_zero _) (equal_symm (equal_of_code (horner_zero C z)))

theorem quotient_delayed_succ (C z N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] equal (delayed (quotient C z N) (succ i)) (horner C z (succ i)) :=
  equal_trans (delayed_succ _ _) (quotient_padded C z N i hi)

theorem quotient_delayed (C z N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] equal (delayed (quotient C z N) i) (horner C z i) := by
  refine .orE (zero_or_succ i) ?_ ?_
  · have h := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := i ≐ zero)
    have e := Prf.eqCongr (Ax := PRAAx) (Γ := (i ≐ zero) :: Γ)
      (delayed (quotient (var 0) (var 1) (var 2)) (var 3) : PTm 4)
      (σ := ![C,z,N,i]) (σ' := ![C,z,N,zero]) (fun j => by fin_cases j <;> first | exact h | exact .eqRefl _)
    have codeEq : (i ≐ zero) :: Γ ⊢[PRAAx] delayed (quotient C z N) i ≐ delayed (quotient C z N) zero := by simpa using e
    exact equal_trans (equal_of_code codeEq)
      (equal_trans (quotient_delayed_zero C z N)
        (equal_symm (equal_of_code (congrAp3 hornerF h (.eqRefl _) (.eqRefl _)))))
  · have h := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := i ≐ succ (pred i))
    have range : (i ≐ succ (pred i)) :: Γ ⊢[PRAAx] lt (pred i) N := le_congr h (.eqRefl _) hi.wk
    have e := Prf.eqCongr (Ax := PRAAx) (Γ := (i ≐ succ (pred i)) :: Γ)
      (delayed (quotient (var 0) (var 1) (var 2)) (var 3) : PTm 4)
      (σ := ![C,z,N,i]) (σ' := ![C,z,N,succ (pred i)]) (fun j => by fin_cases j <;> first | exact h | exact .eqRefl _)
    have codeEq : (i ≐ succ (pred i)) :: Γ ⊢[PRAAx] delayed (quotient C z N) i ≐ delayed (quotient C z N) (succ (pred i)) := by simpa using e
    exact equal_trans (equal_of_code codeEq)
      (equal_trans (quotient_delayed_succ C z N (pred i) range)
        (equal_symm (equal_of_code (congrAp3 hornerF h (.eqRefl _) (.eqRefl _)))))

/-- Every coefficient before the constant tail is exactly reconstructed. -/
theorem coefficient_inside (C z N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    equal (linearCoefficient (quotient C z N) z i) (entry C i) := by
  have q := quotient_padded C z N i hi
  have d := quotient_delayed C z N i (le_trans (le_succ_self _) hi)
  have h := values_of_code (horner_succ (Γ := Γ) C z i)
  have c := padded_inside C i (lt_congr (.eqRefl _) hC.eqSymm (lt_of_lt_of_le hi (le_succ_self N)))
  apply equal_of_values
  · simp only [linearCoefficient,re_sub,re_mul]
    rw [equal_re q,equal_re d,equal_im d,h.1,re_add,re_mul,equal_re c]
    ring
  · simp only [linearCoefficient,im_sub,im_mul]
    rw [equal_im q,equal_re d,equal_im d,h.2,im_add,im_mul,equal_im c]
    ring

/-- The constant coefficient additionally receives the computed remainder. -/
theorem coefficient_tail (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    equal (add (linearCoefficient (quotient C z N) z N) (remainder C z)) (entry C N) := by
  have q := padded_outside (Γ := Γ) (quotient C z N) N (le_congr (quotient_length C z N).eqSymm (.eqRefl _) (le_refl _))
  have d := quotient_delayed (Γ := Γ) C z N N (le_refl _)
  have h := values_of_code (horner_succ (Γ := Γ) C z N)
  have r := values_of_code (Γ := Γ) (a := remainder C z) (b := horner C z (succ N))
    (congrAp3 hornerF hC (.eqRefl _) (.eqRefl _))
  have c := padded_inside C N (lt_congr (.eqRefl _) hC.eqSymm (le_refl _))
  apply equal_of_values
  · simp only [re_add,linearCoefficient,re_sub,re_mul]
    rw [equal_re q,equal_re d,equal_im d,r.1,h.1,re_add,re_mul,equal_re c,re_zero]
    ring
  · simp only [im_add,linearCoefficient,im_sub,im_mul]
    rw [equal_im q,equal_re d,equal_im d,r.2,h.2,im_add,im_mul,equal_im c,im_zero]
    ring

/-! Runtime-prefix evaluation proves the complete polynomial identity. -/

def prefixLaw (C z y N k : PTm n) : Fm PTm n := le k N ⟶
  equal (horner C y (succ k))
    (add (mul (sub y z) (horner (quotient C z N) y k)) (horner C z (succ k)))

@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (C z y N k : PTm n) :
    (prefixLaw C z y N k).subst σ = prefixLaw (Syn.subst σ C) (Syn.subst σ z)
      (Syn.subst σ y) (Syn.subst σ N) (Syn.subst σ k) := by simp [prefixLaw]

theorem prefix_zero (C z y N : PTm n) : Γ ⊢[PRAAx]
    equal (horner C y (succ zero))
      (add (mul (sub y z) (horner (quotient C z N) y zero)) (horner C z (succ zero))) := by
  have a := values_of_code (horner_succ (Γ := Γ) C y zero)
  have b := values_of_code (horner_succ (Γ := Γ) C z zero)
  have az := values_of_code (horner_zero (Γ := Γ) C y)
  have bz := values_of_code (horner_zero (Γ := Γ) C z)
  have qz := values_of_code (horner_zero (Γ := Γ) (quotient C z N) y)
  apply equal_of_values
  · rw [a.1,re_add,re_mul,az.1,az.2,re_add,re_mul,qz.1,qz.2,b.1,re_add,re_mul,bz.1,bz.2,re_zero,im_zero]
    ring
  · rw [a.2,im_add,im_mul,az.1,az.2,im_add,im_mul,qz.1,qz.2,b.2,im_add,im_mul,bz.1,bz.2,re_zero,im_zero]
    ring

theorem prefix_step (C z y N k : PTm n) (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] equal (horner C y (succ k))
      (add (mul (sub y z) (horner (quotient C z N) y k)) (horner C z (succ k)))) : Γ ⊢[PRAAx]
    equal (horner C y (succ (succ k)))
      (add (mul (sub y z) (horner (quotient C z N) y (succ k))) (horner C z (succ (succ k)))) := by
  have a := values_of_code (horner_succ (Γ := Γ) C y (succ k))
  have b := values_of_code (horner_succ (Γ := Γ) C z (succ k))
  have q := values_of_code (horner_succ (Γ := Γ) (quotient C z N) y k)
  have coeff := quotient_padded C z N k hk
  have ir := equal_re ih
  have ii := equal_im ih
  simp only [re_add,im_add,re_mul,im_mul,re_sub,im_sub] at ir ii
  apply equal_of_values
  · rw [a.1,re_add,re_mul,re_add,re_mul,q.1,q.2,b.1,re_add,re_mul]
    simp only [re_add,im_add,re_mul,im_mul,re_sub,im_sub]
    rw [equal_re coeff,equal_im coeff]
    linear_combination ZT.toZ Γ (re y)*ir-ZT.toZ Γ (im y)*ii
  · rw [a.2,im_add,im_mul,im_add,im_mul,q.1,q.2,b.2,im_add,im_mul]
    simp only [re_add,im_add,re_mul,im_mul,re_sub,im_sub]
    rw [equal_re coeff,equal_im coeff]
    linear_combination ZT.toZ Γ (im y)*ir+ZT.toZ Γ (re y)*ii

theorem synthetic_prefix (C z y N k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    equal (horner C y (succ k))
      (add (mul (sub y z) (horner (quotient C z N) y k)) (horner C z (succ k))) := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift z) (Syn.shift y) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨trivial,trivial⟩⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (prefix_zero C z y N)
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := prefixLaw (Syn.shift C) (Syn.shift z) (Syn.shift y) (Syn.shift N) (var 0)
      let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
      exact prefix_step _ _ _ _ _ (Prf.hyp0 (Ax := PRAAx) (Γ := I :: Γ.map Fm.shift))
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C z y N k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all
  exact .impE rule hk

/-- Actual finite synthetic division, at every evaluation point, including
N=0. The only shape premise identifies the input polynomial's true length. -/
theorem division_evaluation (C z y N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    equal (evaluate C y) (add (mul (sub y z) (evaluate (quotient C z N) y)) (remainder C z)) := by
  have h := synthetic_prefix (Γ := Γ) C z y N N (le_refl _)
  have a := values_of_code (Γ := Γ) (a := evaluate C y) (b := horner C y (succ N))
    (congrAp3 hornerF hC (.eqRefl _) (.eqRefl _))
  have b := values_of_code (Γ := Γ) (a := remainder C z) (b := horner C z (succ N))
    (congrAp3 hornerF hC (.eqRefl _) (.eqRefl _))
  have q := values_of_code (Γ := Γ) (a := evaluate (quotient C z N) y) (b := horner (quotient C z N) y N)
    (congrAp3 hornerF (quotient_length C z N) (.eqRefl _) (.eqRefl _))
  apply equal_of_values
  · rw [a.1,re_add,re_mul,q.1,q.2,b.1]
    simpa only [re_add,re_mul] using equal_re h
  · rw [a.2,im_add,im_mul,q.1,q.2,b.2]
    simpa only [im_add,im_mul] using equal_im h

/-- Synthetic division retains the input leading coefficient. -/
theorem quotient_leading (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    equal (entry (quotient C z N) zero) (entry C zero) := by
  have q := values_of_code (quotient_lookup C z N zero hN)
  have h := values_of_code (horner_succ (Γ := Γ) C z zero)
  have hz := values_of_code (horner_zero (Γ := Γ) C z)
  have c := padded_inside C zero (lt_congr (.eqRefl _) hC.eqSymm (zero_lt_succ N))
  apply equal_of_values
  · rw [q.1,h.1,re_add,re_mul,hz.1,hz.2,re_zero,im_zero,equal_re c]; ring
  · rw [q.2,h.2,im_add,im_mul,hz.1,hz.2,re_zero,im_zero,equal_im c]; ring

/-- The quotient is monic of exact represented degree N−1. This includes
N=1, when it is the monic constant polynomial. -/
theorem quotient_monic (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hN : Γ ⊢[PRAAx] le one N) (hMonic : Γ ⊢[PRAAx] equal (entry C zero) oneCode) :
    Γ ⊢[PRAAx] length (quotient C z N) ≐ succ (pred N) ⋏
      equal (entry (quotient C z N) zero) oneCode :=
  .andI ((quotient_length C z N).eqTrans (RationalIntegerNormalization.positive_form hN))
    (equal_trans (quotient_leading C z N hC hN) hMonic)

/-! The actual output pair contains the quotient list and actual remainder. -/

def output (C z N : PTm n) : PTm n := pairT (quotient C z N) (remainder C z)
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C z N : PTm n) : PTm n := ap3 outputF C z N

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C z N : PTm n) :
    Syn.subst σ (output C z N) = output (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C z N : PTm n) :
    Syn.subst σ (run C z N) = run (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ N) := by simp [run]

theorem program_at (C z N : PTm n) : Γ ⊢[PRAAx] run C z N ≐ output C z N := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,z,N]
theorem output_quotient (C z N : PTm n) : Γ ⊢[PRAAx] fstT (run C z N) ≐ quotient C z N :=
  (congrFst (program_at C z N)).eqTrans (fst_pair _ _)
theorem output_remainder (C z N : PTm n) : Γ ⊢[PRAAx] sndT (run C z N) ≐ evaluate C z :=
  (congrSnd (program_at C z N)).eqTrans (snd_pair _ _)

theorem synthetic_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 2) ⟶
      ((lt (var 3) (var 2) ⟶
        equal (linearCoefficient (quotient (var 0) (var 1) (var 2)) (var 1) (var 3)) (entry (var 0) (var 3))) ⋏
      equal (add (linearCoefficient (quotient (var 0) (var 1) (var 2)) (var 1) (var 2)) (remainder (var 0) (var 1)))
        (entry (var 0) (var 2)))) :=
  closeUniv 4 (.impI (.andI (.impI (coefficient_inside _ _ _ _ Prf.hyp1 Prf.hyp0)) (coefficient_tail _ _ _ Prf.hyp0)))

theorem synthetic_division_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 3) ⟶
      equal (evaluate (var 0) (var 2))
        (add (mul (sub (var 2) (var 1)) (evaluate (quotient (var 0) (var 1) (var 3)) (var 2)))
          (remainder (var 0) (var 1)))) :=
  closeUniv 4 (.impI (division_evaluation _ _ _ _ Prf.hyp0))

theorem synthetic_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 2) ⟶ le one (var 2) ⟶ equal (entry (var 0) zero) oneCode ⟶
      (length (quotient (var 0) (var 1) (var 2)) ≐ succ (pred (var 2)) ⋏
        equal (entry (quotient (var 0) (var 1) (var 2)) zero) oneCode)) :=
  closeUniv 3 (.impI (.impI (.impI (quotient_monic _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem synthetic_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (run (var 0) (var 1) (var 2)) ≐ quotient (var 0) (var 1) (var 2)) ⋏
      ((length (quotient (var 0) (var 1) (var 2)) ≐ var 2) ⋏
        (sndT (run (var 0) (var 1) (var 2)) ≐ evaluate (var 0) (var 1)))) :=
  closeUniv 3 (.andI (output_quotient _ _ _) (.andI (quotient_length _ _ _) (output_remainder _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianSyntheticDivision
