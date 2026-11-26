import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFiniteSum

/-!
# Exact reversal of the original Gaussian-rational finite sum

The actual reverse body reads the original body at N-(i+1), preserving
its original numerical data. A genuine QF induction uses the original
first-term split and unconditional successor/monus identity. Original
raw rows remain under actual qadd. The empty sum is included, and no
row canonicality, permutation certificate, or sum identity is input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiniteSumReversal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalFiniteSum (sum termsEqual)
open GaussianRationalHorner (qadd canonical)
open GaussianRationalSyntheticDivision (qadd_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N x : PTm n) : PTm n := pairT N x
def reverseBody (t : PTm 2) : PTm 2 := inst2 t (monus (fstT (var 1)) (succ (var 0))) (sndT (var 1))
def law (t : PTm 2) (N x : PTm n) : Fm PTm n := sum (reverseBody t) N (data N x) ≐ sum t N x

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (N x : PTm n) :
    Syn.subst σ (data N x) = data (Syn.subst σ N) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_law {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (N x : PTm n) :
    (law t N x).subst σ = law t (Syn.subst σ N) (Syn.subst σ x) := by simp [law]

theorem reverse_body_at (t : PTm 2) (i N x : PTm n) : Γ ⊢[PRAAx]
    inst2 (reverseBody t) i (data N x) ≐ inst2 t (monus N (succ i)) x := by
  have shape : inst2 (reverseBody t) i (data N x) =
      inst2 t (monus (fstT (data N x)) (succ i)) (sndT (data N x)) := by
    simp only [reverseBody,inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  rw [shape]
  exact congrInst2 t (congrMonus (fst_pair N x) (.eqRefl _)) (snd_pair N x)

theorem first_at (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    inst2 (reverseBody t) zero (data (succ N) x) ≐ inst2 t N x :=
  (reverse_body_at t zero (succ N) x).eqTrans
    (congrInst2 t ((succ_monus_succ N zero).eqTrans (monus_zero N)) (.eqRefl _))

/-- The old first-term split has exactly the reverse body at count N
as its tail, without any assertion about the generated outer list. -/
theorem shifted_reverse_at (t : PTm 2) (i N x : PTm n) : Γ ⊢[PRAAx]
    inst2 (shiftBody (reverseBody t)) i (data (succ N) x) ≐ inst2 (reverseBody t) i (data N x) := by
  rw [inst2_shiftBody]
  exact (reverse_body_at t (succ i) (succ N) x).eqTrans
    ((congrInst2 t (succ_monus_succ N (succ i)) (.eqRefl _)).eqTrans (reverse_body_at t i N x).eqSymm)

theorem shifted_reverse_sum (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    sum (shiftBody (reverseBody t)) N (data (succ N) x) ≐ sum (reverseBody t) N (data N x) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simpa only [termsEqual,subst_data,Syn.shift,ConciseIPRA.PTm.subst_succ] using
    shifted_reverse_at (Γ := _ :: Γ.map Fm.shift) t (var 0) (Syn.shift N) (Syn.shift x)

theorem reverse_zero (t : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] law t zero x :=
  (GaussianRationalFiniteSum.sum_zero _ _).eqTrans (GaussianRationalFiniteSum.sum_zero t x).eqSymm

theorem reverse_step (t : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] law t N x) : Γ ⊢[PRAAx] law t (succ N) x :=
  (GaussianRationalFiniteSum.sum_shift_first (reverseBody t) N (data (succ N) x)).eqTrans
    ((qadd_congr (first_at t N x) ((shifted_reverse_sum t N x).eqTrans h)).eqTrans
      ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans (GaussianRationalFiniteSum.sum_succ t N x).eqSymm))

/-- Exact CODE equality of the actual original sums, for every internal
count including N=0 and every raw original numerical datum. -/
theorem sum_reverse (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    sum (reverseBody t) N (data N x) ≐ sum t N x := by
  have all : Γ ⊢[PRAAx] .all (law t (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact reverse_zero t x
    · simp only [subst_law,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact reverse_step t _ _ Prf.hyp0
  change Γ ⊢[PRAAx] law t N x
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def reverseSumF (t : PTm 2) : PR 2 := PTm.toPR (sum (reverseBody t) (var 0) (data (var 0) (var 1)))

theorem program_at (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    ap2 (reverseSumF t) N x ≐ sum (reverseBody t) N (data N x) := by
  simpa [reverseSumF,ap2] using toPR_eq (Γ := Γ) (sum (reverseBody t) (var 0) (data (var 0) (var 1)) : PTm 2) ![N,x]

theorem program_original (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] ap2 (reverseSumF t) N x ≐ sum t N x :=
  (program_at t N x).eqTrans (sum_reverse t N x)

theorem actual_original_finite_sum_reversal_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sum (reverseBody t) (var 0) (data (var 0) (var 1)) ≐ sum t (var 0) (var 1)) :=
  closeUniv 2 (sum_reverse t _ _)

theorem actual_reversed_finite_sum_program_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (reverseSumF t) (var 0) (var 1) ≐ sum t (var 0) (var 1) ⋏
      canonical (ap2 (reverseSumF t) (var 0) (var 1))) :=
  closeUniv 2 (.andI (program_original t _ _)
    (GaussianRationalHorner.canonical_congr (program_original t _ _) (GaussianRationalFiniteSum.sum_canonical _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianRationalFiniteSumReversal
