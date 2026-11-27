import IPRADerivations.Foundations.BoundedSyntax

/-!
# Bounded-formula induction through the actual Boolean compiler

The induction formula used by PRA is the quantifier-free equation asserting
that the compiled bit is one. Its proved reflection recovers the original
bounded formula at each stage. The source formula is a fixed finite syntax;
its counter, bounds and other numerical parameters remain internal. Local
hypotheses are preserved and may contain arbitrary formulas.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.BoundedSyntaxInduction

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedSyntax

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem induction (A : BFm (n+1))
    (h0 : Γ ⊢[PRAAx] (formula A).subst (Syn.inst zero))
    (hs : formula A :: Γ.map Fm.shift ⊢[PRAAx] (formula A).subst (repl (succ (var 0)))) :
    Γ ⊢[PRAAx] .all (formula A) := by
  have all : Γ ⊢[PRAAx] .all (bit A var ≐ one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,bit_subst,Syn.subst_var,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
      exact (bounded_reflection A (Syn.inst zero)).iffMpr h0
    · simp only [Fm.subst_eq,bit_subst,Syn.subst_var,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
      have source : (bit A var ≐ one) :: Γ.map Fm.shift ⊢[PRAAx] formula A := by
        simpa only [Fm.subst_id] using (bounded_reflection A var).iffMp Prf.hyp0
      exact (bounded_reflection A (repl (succ (var 0)))).iffMpr (.impE (Prf.impI hs).wk source)
  refine .allI ?_
  simpa only [Fm.subst_id] using (bounded_reflection A var).iffMp all.allOpen

/-- Run bounded induction using a named formula for the reflected invariant. -/
theorem induction_of_formula (A : BFm (n+1)) {P : Fm PTm (n+1)} (h : formula A = P)
    (h0 : Γ ⊢[PRAAx] P.subst (Syn.inst zero))
    (hs : P :: Γ.map Fm.shift ⊢[PRAAx] P.subst (repl (succ (var 0)))) :
    Γ ⊢[PRAAx] .all (formula A) := by
  subst P
  exact induction A h0 hs

theorem induction_at (A : BFm (n+1)) (k : PTm n)
    (h0 : Γ ⊢[PRAAx] (formula A).subst (Syn.inst zero))
    (hs : formula A :: Γ.map Fm.shift ⊢[PRAAx] (formula A).subst (repl (succ (var 0)))) :
    Γ ⊢[PRAAx] (formula A).subst (Syn.inst k) := (induction A h0 hs).allE k

theorem induction_rule (A : BFm (n+1)) : Γ ⊢[PRAAx]
    ((formula A).subst (Syn.inst zero) ⟶
      (.all (formula A ⟶ (formula A).subst (repl (succ (var 0)))) ⟶ .all (formula A))) := by
  refine .impI (.impI (induction A Prf.hyp1 ?_))
  have hLocal := (Prf.hyp0 (Ax := PRAAx) (Γ := (formula A).subst (Syn.inst zero) :: Γ)
    (φ := .all (formula A ⟶ (formula A).subst (repl (succ (var 0)))))).allOpen
  exact .impE hLocal.wk Prf.hyp0

theorem bounded_induction_closed (A : BFm (n+1)) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ n
    ((formula A).subst (Syn.inst zero) ⟶
      (.all (formula A ⟶ (formula A).subst (repl (succ (var 0)))) ⟶ .all (formula A))) :=
  closeUniv n (induction_rule A)

end LeanProofs.IPRA.Foundations.BoundedSyntaxInduction
