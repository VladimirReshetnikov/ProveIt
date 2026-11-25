import IPRADerivations.Core.Powers

/-!
# Parity in iPRA

`par 0 = 0`, `par (x + 1) = 1 ∸ par x`, and `half 0 = 0`, `half (x + 1) = half x + par x`.
Derived:

* `half_par`: `x = 2 half x + par x`, with `par x = 0 ∨ par x = 1`;
* `even_or_odd`: `x = 2h ∨ x = 2h + 1` for `h = half x`;
* `par_double`, `par_double_succ`: `par (2k) = 0`, `par (2k + 1) = 1`;
* `even_ne_odd`: `2k = 2m + 1` is absurd.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The numeral `2`. -/
abbrev two : PTm n := succ one

/-- `par`. -/
abbrev parF : PR 1 := rec1 zero (monus one (var 1))
abbrev par (x : PTm n) : PTm n := ap1 parF x

theorem par_zero : Γ ⊢[PRAAx] par (zero : PTm n) ≐ zero := by
  simpa using rec1_zero (Γ := Γ) zero (monus one (var 1))

theorem par_succ (x : PTm n) : Γ ⊢[PRAAx] par (succ x) ≐ monus one (par x) := by
  have h := rec1_succ (Γ := Γ) zero (monus one (var 1)) x
  simp only [PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Matrix.cons_val_one, Matrix.head_cons] at h
  exact h

/-- `half`. -/
abbrev halfF : PR 1 := rec1 zero (var 1 + par (var 0))
abbrev half (x : PTm n) : PTm n := ap1 halfF x

theorem half_zero : Γ ⊢[PRAAx] half (zero : PTm n) ≐ zero := by
  simpa using rec1_zero (Γ := Γ) zero (var 1 + par (var 0))

theorem half_succ (x : PTm n) : Γ ⊢[PRAAx] half (succ x) ≐ half x + par x := by
  have h := rec1_succ (Γ := Γ) zero (var 1 + par (var 0)) x
  simp only [PTm.subst_add, subst_ap1, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h
  exact h

theorem monus_one_zero : Γ ⊢[PRAAx] monus (one : PTm n) zero ≐ one := monus_zero _
theorem monus_one_one : Γ ⊢[PRAAx] monus (one : PTm n) one ≐ zero := monus_self _

/-- `x = 2 half x + par x ∧ (par x = 0 ∨ par x = 1)`. -/
private abbrev hpF : Fm PTm 1 :=
  (var 0 ≐ two * half (var 0) + par (var 0)) ⋏ ((par (var 0) ≐ zero) ⋎ (par (var 0) ≐ one))

private theorem half_par₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] hpF := by
  refine ind _ ⟨trivial, trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_and, Fm.subst_or, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap1,
      Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .andI ?_ (.orI₁ par_zero)
    refine withEq par_zero fun e₁ => withEq half_zero fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
  · simp only [Fm.subst_and, Fm.subst_or, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap1,
      Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ,
      PTm.subst_monus]
    have hx : [hpF] ⊢[PRAAx] var 0 ≐ two * half (var 0) + par (var 0) := .andE₁ Prf.hyp0
    refine .orE (.andE₂ Prf.hyp0) ?_ ?_
    · -- par x = 0: par (x+1) = 1, half (x+1) = half x.
      have hp : ((par (var 0) ≐ zero) :: [hpF]) ⊢[PRAAx] par (succ (var 0)) ≐ one :=
        (par_succ _).eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans monus_one_zero)
      refine .andI ?_ (.orI₂ hp)
      refine withEq hx.wk fun e₁ => withEq Prf.hyp0 fun e₂ => withEq hp fun e₃ =>
        withEq (half_succ (var 0)) fun e₄ => ?_
      apply deriveNat; ipra_simps; rw [e₃, e₄]; rw [e₂] at e₁ ⊢; linear_combination e₁
    · -- par x = 1: par (x+1) = 0, half (x+1) = half x + 1.
      have hp : ((par (var 0) ≐ one) :: [hpF]) ⊢[PRAAx] par (succ (var 0)) ≐ zero :=
        (par_succ _).eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans monus_one_one)
      refine .andI ?_ (.orI₁ hp)
      refine withEq hx.wk fun e₁ => withEq Prf.hyp0 fun e₂ => withEq hp fun e₃ =>
        withEq (half_succ (var 0)) fun e₄ => ?_
      apply deriveNat; ipra_simps; rw [e₃, e₄]; rw [e₂] at e₁ e₄ ⊢; linear_combination e₁

theorem half_par (x : PTm n) : Γ ⊢[PRAAx] x ≐ two * half x + par x := by
  have h := inst (Γ := Γ) half_par₀ ![x]
  simp at h
  exact .andE₁ h

theorem par_cases (x : PTm n) : Γ ⊢[PRAAx] (par x ≐ zero) ⋎ (par x ≐ one) := by
  have h := inst (Γ := Γ) half_par₀ ![x]
  simp at h
  exact .andE₂ h

/-- `x = 2h ∨ x = 2h + 1` with `h = half x`. -/
theorem even_or_odd (x : PTm n) :
    Γ ⊢[PRAAx] (x ≐ two * half x) ⋎ (x ≐ two * half x + one) := by
  refine .orE (par_cases x) ?_ ?_
  · exact .orI₁ ((half_par x).eqTrans ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)))
  · exact .orI₂ ((half_par x).eqTrans (congrAdd (.eqRefl _) Prf.hyp0))

/-- Variables: `0 = k`. `par (2k) = 0`. -/
private abbrev pdF : Fm PTm 1 := par (two * var 0) ≐ zero

private theorem par_double₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] pdF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap1, Syn.subst_var, Syn.inst_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact (congrAp1 parF (mul_zero _)).eqTrans par_zero
  · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap1, Syn.subst_var, Syn.repl_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    -- 2 (k + 1) = S (S (2k)).
    have e : [pdF] ⊢[PRAAx] two * succ (var 0) ≐ succ (succ (two * var 0)) := by
      ipra_ring
    refine (congrAp1 parF e).eqTrans ((par_succ _).eqTrans ?_)
    refine (congrMonus (.eqRefl _) ((par_succ _).eqTrans
      ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans monus_one_zero))).eqTrans monus_one_one

theorem par_double (k : PTm n) : Γ ⊢[PRAAx] par (two * k) ≐ zero := by
  simpa using inst (Γ := Γ) par_double₀ ![k]

theorem par_double_succ (k : PTm n) : Γ ⊢[PRAAx] par (two * k + one) ≐ one := by
  have e : Γ ⊢[PRAAx] two * k + one ≐ succ (two * k) := (succ_eq_add_one _).eqSymm
  exact (congrAp1 parF e).eqTrans ((par_succ _).eqTrans
    ((congrMonus (.eqRefl _) (par_double k)).eqTrans monus_one_zero))

/-- `2k = 2m + 1` is absurd. -/
theorem even_ne_odd {k m : PTm n} (φ : Fm PTm n) (h : Γ ⊢[PRAAx] two * k ≐ two * m + one) :
    Γ ⊢[PRAAx] φ :=
  succ_ne_zero' φ (a := zero) ((par_double_succ m).eqSymm.eqTrans
    ((congrAp1 parF h).eqSymm.eqTrans (par_double k)))

end LeanProofs.IPRA
