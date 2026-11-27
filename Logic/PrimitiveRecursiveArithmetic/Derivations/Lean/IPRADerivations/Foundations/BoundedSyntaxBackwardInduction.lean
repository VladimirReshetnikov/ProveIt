import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Backward induction for the actual arity-indexed bounded syntax

A single terminal observation and genuine one-step backward transfers give
every observation below the internal terminal bound. The induction runs on
the Boolean compilation of the guarded reverse-counter syntax. Only one
fixed finite bounded formula is external; the terminal bound, reverse
counter, queried index and other numerical parameters remain internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.BoundedSyntaxBackwardInduction

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedSyntax

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Substitution identities express only capture-avoiding syntax. -/
theorem up_shift {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift,Syn.shift_subst]
  simp

theorem shifted_shift_inst (s : PTm n) (t : PTm (n+1)) :
    Syn.subst (Syn.inst t) (Syn.subst (Syn.up (fun i => var i.succ)) (Syn.shift s)) = Syn.shift s := by
  rw [up_shift,Syn.subst_inst_shift]
  rfl

theorem repl_inst (φ : Fm PTm (n+1)) (t : PTm (n+1)) (j : PTm n) :
    (φ.subst (repl t)).subst (Syn.inst j) = φ.subst (Syn.inst (Syn.subst (Syn.inst j) t)) := by
  rw [Fm.subst_subst]
  congr 1
  funext i
  cases i using Fin.cases <;> simp

theorem repl_repl (φ : Fm PTm (n+1)) (s t : PTm (n+1)) :
    (φ.subst (repl s)).subst (repl t) = φ.subst (repl (Syn.subst (repl t) s)) := by
  rw [Fm.subst_subst]
  congr 1
  funext i
  cases i using Fin.cases <;> simp

theorem shifted_inst (φ : Fm PTm (n+1)) (t : PTm (n+1)) :
    (φ.subst (Syn.up (fun i => var i.succ))).subst (Syn.inst t) = φ.subst (repl t) := by
  rw [Fm.subst_subst]
  congr 1
  funext i
  cases i using Fin.cases <;> simp [Syn.shift]

theorem repl_identity (φ : Fm PTm (n+1)) : φ.subst (repl (var 0)) = φ := by
  have e : (repl (var 0) : Fin (n+1) → PTm (n+1)) = var := by
    funext i
    cases i using Fin.cases <;> simp
  rw [e,Fm.subst_id]

theorem inst_congr (φ : Fm PTm (n+1)) {a b : PTm n}
    (h : Γ ⊢[PRAAx] a ≐ b) (ha : Γ ⊢[PRAAx] φ.subst (Syn.inst a)) : Γ ⊢[PRAAx]
    φ.subst (Syn.inst b) :=
  .eqSubst φ (Syn.inst a) (Syn.inst b) (fun i => by
    cases i using Fin.cases
    · exact h
    · exact .eqRefl _) ha

theorem repl_congr (φ : Fm PTm (n+1)) {Δ : List (Fm PTm (n+1))} {a b : PTm (n+1)}
    (h : Δ ⊢[PRAAx] a ≐ b) (ha : Δ ⊢[PRAAx] φ.subst (repl a)) : Δ ⊢[PRAAx]
    φ.subst (repl b) :=
  .eqSubst φ (repl a) (repl b) (fun i => by
    cases i using Fin.cases
    · exact h
    · exact .eqRefl _) ha

theorem reverse_le (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] le (monus N j) N :=
  le_of_eq_add ((eq_add_of_le hj).eqTrans (add_comm _ _))

theorem reverse_complement (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    monus N (monus N j) ≐ j :=
  (congrMonus (eq_add_of_le hj) (.eqRefl _)).eqTrans (add_monus _ _)

theorem reverse_successor (N t : PTm n) (ht : Γ ⊢[PRAAx] lt t N) : Γ ⊢[PRAAx]
    succ (monus N (succ t)) ≐ monus N t := by
  have e : Γ ⊢[PRAAx] N ≐ succ (monus N (succ t))+t :=
    (eq_add_of_le ht).eqTrans (by ipra_ring)
  exact ((congrMonus e (.eqRefl t)).eqTrans (add_monus _ _)).eqSymm

alias reverse_strict := LeanProofs.IPRA.Common.monus_succ_lt

def localStep (A : BFm (n+1)) (N : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    (formula A).subst (repl (succ (var 0))) ⟶ formula A)

def reverseSyntax (A : BFm (n+1)) (N : PTm n) : BFm (n+1) :=
  .imp (.le (var 0) (Syn.shift N)) (A.subst (repl (monus (Syn.shift N) (var 0))))

theorem reverse_formula (A : BFm (n+1)) (N : PTm n) :
    formula (reverseSyntax A N) =
      (le (var 0) (Syn.shift N) ⟶ (formula A).subst (repl (monus (Syn.shift N) (var 0)))) := by
  simp only [reverseSyntax,formula,formula_subst,BFm.le,le]

/-- The only induction is the existing QF induction on the compiler bit. -/
theorem reverse_induction (A : BFm (n+1)) (N : PTm n)
    (hTerminal : Γ ⊢[PRAAx] (formula A).subst (Syn.inst N))
    (hStep : Γ ⊢[PRAAx] localStep A N) : Γ ⊢[PRAAx] .all (formula (reverseSyntax A N)) := by
  apply BoundedSyntaxInduction.induction
  · simp only [reverse_formula, Fm.subst_imp, subst_le, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, repl_inst,
      PTm.subst_monus]
    exact .impI (inst_congr (formula A) (monus_zero N).eqSymm hTerminal.wk)
  · simp only [reverse_formula,Fm.subst_imp,subst_le,Syn.subst_var,Syn.repl_zero,
      subst_repl_shift,repl_repl,PTm.subst_monus]
    refine .impI ?_
    let Δ := le (succ (var 0)) (Syn.shift N) ::
      (le (var 0) (Syn.shift N) ⟶ (formula A).subst (repl (monus (Syn.shift N) (var 0)))) :: Γ.map Fm.shift
    have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
    have previousGuard : Δ ⊢[PRAAx]
        le (var 0) (Syn.shift N) ⟶ (formula A).subst (repl (monus (Syn.shift N) (var 0))) := by
      exact Prf.hyp1
    have previous := Prf.impE previousGuard (le_of_lt range)
    let r := monus (Syn.shift N) (succ (var 0))
    have successor : Δ ⊢[PRAAx] (formula A).subst (repl (succ r)) :=
      repl_congr (formula A) (reverse_successor (Syn.shift N) (var 0) range).eqSymm previous
    have shifted : Γ.map Fm.shift ⊢[PRAAx]
        lt r (Syn.shift N) ⟶ (formula A).subst (repl (succ r)) ⟶ (formula A).subst (repl r) := by
      simpa only [localStep,Fm.shift,Fm.subst_all,shifted_inst,Fm.subst_imp,subst_lt,
        Syn.subst_var,Syn.up_zero,Syn.inst_zero,shifted_shift_inst,
        Syn.repl_zero,subst_repl_shift,repl_repl,ConciseIPRA.PTm.subst_succ] using hStep.shift.allE r
    exact .impE (.impE shifted.wk.wk (reverse_strict (Syn.shift N) (var 0) range)) successor

theorem backward_induction (A : BFm (n+1)) (N : PTm n)
    (hTerminal : Γ ⊢[PRAAx] (formula A).subst (Syn.inst N))
    (hStep : Γ ⊢[PRAAx] localStep A N) : Γ ⊢[PRAAx]
    .all (le (var 0) (Syn.shift N) ⟶ formula A) := by
  have reversed := reverse_induction A N hTerminal hStep
  refine .allI (.impI ?_)
  let Δ := le (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := Prf.hyp0
  have atReverse : Γ.map Fm.shift ⊢[PRAAx]
      le (monus (Syn.shift N) (var 0)) (Syn.shift N) ⟶
        (formula A).subst (repl (monus (Syn.shift N) (monus (Syn.shift N) (var 0)))) := by
    simpa only [Fm.shift,Fm.subst_all,shifted_inst,reverse_formula,Fm.subst_imp,
      subst_le,Syn.subst_var,Syn.up_zero,Syn.inst_zero,shifted_shift_inst,
      Syn.repl_zero,subst_repl_shift,repl_repl,PTm.subst_monus] using
      reversed.shift.allE (monus (Syn.shift N) (var 0))
  have actual := Prf.impE atReverse.wk (reverse_le (Syn.shift N) (var 0) range)
  have recovered := repl_congr (formula A) (reverse_complement (Syn.shift N) (var 0) range) actual
  simpa only [repl_identity] using recovered

theorem backward_induction_at (A : BFm (n+1)) (N j : PTm n)
    (hTerminal : Γ ⊢[PRAAx] (formula A).subst (Syn.inst N))
    (hStep : Γ ⊢[PRAAx] localStep A N) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    (formula A).subst (Syn.inst j) := by
  have h : Γ ⊢[PRAAx] le j N ⟶ (formula A).subst (Syn.inst j) := by
    simpa only [Fm.subst_imp,subst_le,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (backward_induction A N hTerminal hStep).allE j
  exact .impE h hj

theorem local_step_at (A : BFm (n+1)) (N j : PTm n)
    (hStep : Γ ⊢[PRAAx] localStep A N) (hj : Γ ⊢[PRAAx] lt j N)
    (hNext : Γ ⊢[PRAAx] (formula A).subst (Syn.inst (succ j))) : Γ ⊢[PRAAx]
    (formula A).subst (Syn.inst j) := by
  have h : Γ ⊢[PRAAx] lt j N ⟶ (formula A).subst (Syn.inst (succ j)) ⟶ (formula A).subst (Syn.inst j) := by
    simpa only [localStep,Fm.subst_imp,subst_lt,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,
      repl_inst,ConciseIPRA.PTm.subst_succ] using hStep.allE j
  exact .impE (.impE h hj) hNext

/-- The inference-rule form retains arbitrary local hypotheses. -/
theorem backward_induction_of_local (A : BFm (n+1)) (N : PTm n)
    (hTerminal : Γ ⊢[PRAAx] (formula A).subst (Syn.inst N))
    (hLocal : (formula A).subst (repl (succ (var 0))) ::
      lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] formula A) : Γ ⊢[PRAAx]
    .all (le (var 0) (Syn.shift N) ⟶ formula A) :=
  backward_induction A N hTerminal (.allI (.impI (.impI hLocal)))

theorem backward_induction_at_of_local (A : BFm (n+1)) (N j : PTm n)
    (hTerminal : Γ ⊢[PRAAx] (formula A).subst (Syn.inst N))
    (hLocal : (formula A).subst (repl (succ (var 0))) ::
      lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] formula A)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] (formula A).subst (Syn.inst j) :=
  backward_induction_at A N j hTerminal (.allI (.impI (.impI hLocal))) hj

theorem backward_induction_rule (A : BFm (n+1)) (N : PTm n) : Γ ⊢[PRAAx]
    ((formula A).subst (Syn.inst N) ⟶ localStep A N ⟶ .all (le (var 0) (Syn.shift N) ⟶ formula A)) :=
  .impI (.impI (backward_induction A N Prf.hyp1 Prf.hyp0))

theorem backward_induction_at_rule (A : BFm (n+1)) (N j : PTm n) : Γ ⊢[PRAAx]
    ((formula A).subst (Syn.inst N) ⟶ localStep A N ⟶ le j N ⟶ (formula A).subst (Syn.inst j)) :=
  .impI (.impI (.impI (backward_induction_at A N j Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))

/-- Closing the actual free numerical variables does not quantify over
formula syntax or assume an internal universal formula evaluator. -/
theorem bounded_backward_induction_closed (A : BFm (n+1)) (N : PTm n) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ n
      ((formula A).subst (Syn.inst N) ⟶ localStep A N ⟶ .all (le (var 0) (Syn.shift N) ⟶ formula A)) :=
  closeUniv n (backward_induction_rule A N)

theorem bounded_backward_induction_at_closed (A : BFm (n+1)) (N j : PTm n) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ n
      ((formula A).subst (Syn.inst N) ⟶ localStep A N ⟶ le j N ⟶ (formula A).subst (Syn.inst j)) :=
  closeUniv n (backward_induction_at_rule A N j)

theorem compiled_reverse_induction_closed (A : BFm (n+1)) (N : PTm n) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ n
      ((formula A).subst (Syn.inst N) ⟶ localStep A N ⟶ .all (formula (reverseSyntax A N))) :=
  closeUniv n (.impI (.impI (reverse_induction A N Prf.hyp1 Prf.hyp0)))

theorem reverse_complement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 1) (var 0) ⟶ monus (var 0) (monus (var 0) (var 1)) ≐ var 1) :=
  closeUniv 2 (.impI (reverse_complement _ _ Prf.hyp0))

theorem reverse_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶ succ (monus (var 0) (succ (var 1))) ≐ monus (var 0) (var 1)) :=
  closeUniv 2 (.impI (reverse_successor _ _ Prf.hyp0))

end LeanProofs.IPRA.Foundations.BoundedSyntaxBackwardInduction
