import IPRADerivations.Foundations.RuntimePermutationDeletion
import IPRADerivations.Topology.InjectionBound

/-!
# The retained runtime permutation count is bounded by the actual factorial

An actual retained word of size m+1 is mapped to its maximum position
and the existing retained rank of its actual deletion. The proved bounded
pair code is injective. Numerical finite injection counting yields the
successor bound; ordinary quantifier-free induction yields count(m)<=m!.
No host dimension, cardinality interpretation or factorial-count premise
is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RuntimePermutationFactorialBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RuntimePermutationWords (count words horizon permutationBit)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.RuntimePermutationDeletion (packed packed_bound packed_unique)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def retained (m r : PTm n) : PTm n := entry (words (succ m)) r
def packing (m r : PTm n) : PTm n := packed m (retained m r)
def packingBody : PTm 2 := packing (var 1) (var 0)
def packingF : PR 2 := PTm.toPR packingBody
def factorial (m : PTm n) : PTm n := ap2 factF m zero
@[simp] theorem subst_retained {l : ℕ} (σ : Fin n → PTm l) (m r : PTm n) :
    Syn.subst σ (retained m r) = retained (Syn.subst σ m) (Syn.subst σ r) := by simp [retained]
@[simp] theorem subst_packing {l : ℕ} (σ : Fin n → PTm l) (m r : PTm n) :
    Syn.subst σ (packing m r) = packing (Syn.subst σ m) (Syn.subst σ r) := by simp [packing]
@[simp] theorem subst_factorial {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (factorial m) = factorial (Syn.subst σ m) := by simp [factorial]
theorem packing_at (m r : PTm n) : Γ ⊢[PRAAx] ap2 packingF r m ≐ packing m r := by
  simpa [packingF,packingBody,ap2] using toPR_eq (Γ := Γ) packingBody ![r,m]
theorem retained_bound (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count (succ m))) : Γ ⊢[PRAAx] lt (retained m r) (horizon (succ m)) :=
  RuntimePermutationWords.retained_bound _ _ hr
theorem retained_checker (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count (succ m))) : Γ ⊢[PRAAx] permutationBit (succ m) (retained m r) ≐ one :=
  (RuntimePermutationWords.checker_reflection _ _).iffMpr (RuntimePermutationWords.retained_valid _ _ hr)
theorem packing_bound (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count (succ m))) : Γ ⊢[PRAAx] lt (ap2 packingF r m) (count m*succ m) :=
  lt_congr (packing_at m r).eqSymm (.eqRefl _) (packed_bound _ _ (retained_bound m r hr) (retained_checker m r hr))
theorem packing_unique (m r s : PTm n) (hr : Γ ⊢[PRAAx] lt r (count (succ m))) (hs : Γ ⊢[PRAAx] lt s (count (succ m)))
    (he : Γ ⊢[PRAAx] ap2 packingF r m ≐ ap2 packingF s m) : Γ ⊢[PRAAx] r ≐ s :=
  RuntimePermutationWords.retained_position_unique _ _ _ hr hs
    (packed_unique _ _ _ (retained_bound m r hr) (retained_bound m s hs) (retained_checker m r hr) (retained_checker m s hs)
      ((packing_at m r).eqSymm.eqTrans (he.eqTrans (packing_at m s))))
theorem packing_different (m r s : PTm n) (hrs : Γ ⊢[PRAAx] lt r s) (hs : Γ ⊢[PRAAx] lt s (count (succ m))) : Γ ⊢[PRAAx]
    neg (ap2 packingF r m ≐ ap2 packingF s m) :=
  .impI (.impE (RuntimeAdjacentPermutationSwap.different_of_lt hrs).wk
    (packing_unique m r s (lt_of_lt_of_le hrs (le_of_lt hs)).wk hs.wk Prf.hyp0))

theorem successor_count_bound (m : PTm n) : Γ ⊢[PRAAx] le (count (succ m)) (count m*succ m) := by
  apply Topology.InjectionBound.injection_bound packingF (d := count (succ m)) (m := count m*succ m) (x := m)
  · refine .allI (.impI ?_)
    have hr : lt (var 0) (Syn.shift (count (succ m))) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (count (succ (Syn.shift m))) := by
      simpa [Syn.shift] using (Prf.hyp0 : lt (var 0) (Syn.shift (count (succ m))) :: Γ.map Fm.shift ⊢[PRAAx] _)
    simpa only [Syn.shift,RuntimePermutationWords.subst_count,PTm.subst_mul,ConciseIPRA.PTm.subst_succ] using packing_bound (Syn.shift m) (var 0) hr
  · refine .allI (.allI (.impI (.impI ?_)))
    let Δ := lt (var 0) (Syn.shift (Syn.shift (count (succ m)))) :: lt (var 1) (var 0) :: (Γ.map Fm.shift).map Fm.shift
    have hs : Δ ⊢[PRAAx] lt (var 0) (count (succ (Syn.shift (Syn.shift m)))) := by
      simpa [Δ,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift (count (succ m)))))
    exact packing_different _ _ _ Prf.hyp1 hs
theorem factorial_zero : Γ ⊢[PRAAx] factorial (zero : PTm n) ≐ one := fact_zero zero
theorem factorial_succ (m : PTm n) : Γ ⊢[PRAAx] factorial (succ m) ≐ factorial m*succ m := fact_succ m zero
theorem count_factorial_bound (m : PTm n) : Γ ⊢[PRAAx] le (count m) (factorial m) := by
  have all : Γ ⊢[PRAAx] .all (le (count (var 0)) (factorial (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le,RuntimePermutationWords.subst_count,subst_factorial,Syn.subst_var,Syn.inst_zero]
      exact le_congr RuntimePermutationWords.count_zero.eqSymm factorial_zero.eqSymm (le_refl one)
    · simp only [subst_le,RuntimePermutationWords.subst_count,subst_factorial,Syn.subst_var,Syn.repl_zero]
      exact le_congr (.eqRefl _) (factorial_succ (var 0)).eqSymm
        (le_trans (successor_count_bound (var 0)) (mul_le_mul_right (succ (var 0)) Prf.hyp0))
  simpa only [subst_le,RuntimePermutationWords.subst_count,subst_factorial,Syn.subst_var,Syn.inst_zero] using all.allE m

def output (m : PTm n) : PTm n := pairT (count m) (factorial m)
def outputF : PR 1 := PTm.toPR (output (var 0))
def run (m : PTm n) : PTm n := ap1 outputF m
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (output m) = output (Syn.subst σ m) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (run m) = run (Syn.subst σ m) := by simp [run]
theorem program_at (m : PTm n) : Γ ⊢[PRAAx] run m ≐ output m := by
  simpa [run,outputF,ap1] using toPR_eq (Γ := Γ) (output (var 0) : PTm 1) ![m]
theorem returned_count (m : PTm n) : Γ ⊢[PRAAx] fstT (run m) ≐ count m := (congrFst (program_at m)).eqTrans (fst_pair _ _)
theorem returned_factorial (m : PTm n) : Γ ⊢[PRAAx] sndT (run m) ≐ factorial m := (congrSnd (program_at m)).eqTrans (snd_pair _ _)
theorem returned_bound (m : PTm n) : Γ ⊢[PRAAx] le (fstT (run m)) (sndT (run m)) :=
  le_congr (returned_count m).eqSymm (returned_factorial m).eqSymm (count_factorial_bound m)

theorem actual_packing_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (count (succ (var 0))) ⟶ lt (ap2 packingF (var 1) (var 0)) (count (var 0)*succ (var 0))) :=
  closeUniv 2 (.impI (packing_bound _ _ Prf.hyp0))
theorem actual_packing_injective_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (count (succ (var 0))) ⟶ lt (var 2) (count (succ (var 0))) ⟶
      ap2 packingF (var 1) (var 0) ≐ ap2 packingF (var 2) (var 0) ⟶ var 1 ≐ var 2) :=
  closeUniv 3 (.impI (.impI (.impI (packing_unique _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_successor_count_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (count (succ (var 0))) (count (var 0)*succ (var 0))) := closeUniv 1 (successor_count_bound _)
theorem actual_factorial_count_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (count (var 0)) (factorial (var 0))) := closeUniv 1 (count_factorial_bound _)
theorem actual_count_bound_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (run (var 0) ≐ output (var 0)) := closeUniv 1 (program_at _)
theorem actual_returned_factorial_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (fstT (run (var 0))) (sndT (run (var 0)))) := closeUniv 1 (returned_bound _)

end LeanProofs.IPRA.Foundations.RuntimePermutationFactorialBound
