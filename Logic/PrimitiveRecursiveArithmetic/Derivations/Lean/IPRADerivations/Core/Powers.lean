import IPRADerivations.Core.Pairing

/-!
# Powers and squares in iPRA

With `pw a m = aᵐ` (the symbol `powF` of `Core.Definitions`):

* `pw_add`: `a^{m+k} = aᵐ aᵏ`;
* `pw_le_pw`: `a ≤ b → aᵐ ≤ bᵐ`;
* `pw_one_le`, `pw_le_pw_exp`: for a base at least one, powers stay at least one and increase with the exponent;
* `le_self_pw`: `S a ≤ (S a)^{S m}`;
* `no_square_between`: there is no square strictly between `k²` and `(k + 1)²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `aᵐ`. -/
abbrev pw (a m : PTm n) : PTm n := ap2 powF m a

theorem pw_zero (a : PTm n) : Γ ⊢[PRAAx] pw a zero ≐ one := pow_zero' a
theorem pw_succ (a m : PTm n) : Γ ⊢[PRAAx] pw a (succ m) ≐ pw a m * a := pow_succ' m a

theorem pw_one (a : PTm n) : Γ ⊢[PRAAx] pw a one ≐ a :=
  (pw_succ a zero).eqTrans ((congrMul (pw_zero a) (.eqRefl a)).eqTrans (one_mul a))

/-- Substitution normal forms, including powers. -/
macro "pw_subst" : tactic =>
  `(tactic| simp only [Fm.subst_eq, Fm.subst_imp, Fm.subst_and, Fm.subst_or, subst_le, subst_lt,
      PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_succ, Syn.repl_zero, Syn.repl_succ, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ, inst_two, inst_three, repl_one, repl_two, repl_three])

/-- Every power of one is one. -/
theorem pw_base_one (e : PTm n) : Γ ⊢[PRAAx] pw one e ≐ one := by
  have all : Γ ⊢[PRAAx] Fm.all (pw one (var 0) ≐ one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa using pw_zero (Γ := Γ) (one : PTm n)
    · pw_subst
      exact (pw_succ _ _).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _))
  simpa using all.allE e

/-- Variables: `0 = k` (induction), `1 = m`, `2 = a`. -/
private abbrev pwAddF : Fm PTm 3 := pw (var 2) (var 1 + var 0) ≐ pw (var 2) (var 1) * pw (var 2) (var 0)

private theorem pw_add₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] pwAddF := by
  refine ind _ trivial ?_ ?_
  · pw_subst
    exact (congrAp2 powF (add_zero _) (.eqRefl _)).eqTrans
      ((mul_comm _ _).eqTrans ((congrMul (pw_zero _) (.eqRefl _)).eqTrans (one_mul _))).eqSymm
  · pw_subst
    refine (congrAp2 powF (add_succ _ _) (.eqRefl _)).eqTrans ?_
    refine (pw_succ _ _).eqTrans ?_
    refine (congrMul Prf.hyp0 (.eqRefl _)).eqTrans ?_
    exact (mul_assoc _ _ _).eqTrans (congrMul (.eqRefl _) (pw_succ _ _).eqSymm)

theorem pw_add (a m k : PTm n) : Γ ⊢[PRAAx] pw a (m + k) ≐ pw a m * pw a k := by
  simpa using inst (Γ := Γ) pw_add₀ (![k, m, a] : Fin 3 → PTm n)

/-- Variables: `0 = m` (induction), `1 = a`, `2 = b`. -/
private abbrev pwLeF : Fm PTm 3 := le (var 1) (var 2) ⟶ le (pw (var 1) (var 0)) (pw (var 2) (var 0))

private theorem pw_le_pw₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] pwLeF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · pw_subst
    exact .impI (le_congr (pw_zero _).eqSymm (pw_zero _).eqSymm (le_refl _))
  · pw_subst
    refine .impI ?_
    have hab : _ ⊢[PRAAx] le (var 1) (var 2) := (Prf.hyp0 : (le (var 1) (var 2) :: [pwLeF]) ⊢[PRAAx] _)
    have ih : (le (var 1) (var 2) :: [pwLeF]) ⊢[PRAAx] le (pw (var 1) (var 0)) (pw (var 2) (var 0)) :=
      .impE Prf.hyp1 Prf.hyp0
    refine le_congr (pw_succ _ _).eqSymm (pw_succ _ _).eqSymm ?_
    refine le_trans (mul_le_mul_right (var 1) ih) ?_
    exact mul_le_mul_left (pw (var 2) (var 0)) hab

theorem pw_le_pw {a b : PTm n} (m : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (pw a m) (pw b m) := by
  have i := inst (Γ := Γ) pw_le_pw₀ (![m, a, b] : Fin 3 → PTm n)
  simp at i
  exact .impE i h

/-- Every power of a base at least one is at least one. -/
theorem pw_one_le {a : PTm n} (ha : Γ ⊢[PRAAx] le one a) (m : PTm n) :
    Γ ⊢[PRAAx] le one (pw a m) :=
  le_congr (pw_base_one m) (.eqRefl _) (pw_le_pw m ha)

/-- Powers of a base at least one are nondecreasing in the exponent. -/
theorem pw_le_pw_exp {a m k : PTm n} (ha : Γ ⊢[PRAAx] le one a) (hmk : Γ ⊢[PRAAx] le m k) :
    Γ ⊢[PRAAx] le (pw a m) (pw a k) := by
  have expansion := (congrAp2 powF (eq_add_of_le hmk) (.eqRefl a)).eqTrans (pw_add a m (monus k m))
  exact le_congr ((mul_comm _ _).eqTrans (one_mul _)) expansion.eqSymm
    (mul_le_mul_left (pw a m) (pw_one_le ha (monus k m)))

theorem le_self_pw (a m : PTm n) : Γ ⊢[PRAAx] le (succ a) (pw (succ a) (succ m)) :=
  le_congr (pw_one _) (.eqRefl _)
    (pw_le_pw_exp ((succ_monus_succ zero a).eqTrans (zero_le a))
      ((succ_monus_succ zero m).eqTrans (zero_le m)))

/-- No square lies strictly between `k²` and `(k + 1)²`. -/
theorem no_square_between {k y : PTm n} (φ : Fm PTm n) (h₁ : Γ ⊢[PRAAx] lt (k * k) (y * y))
    (h₂ : Γ ⊢[PRAAx] lt (y * y) ((k + one) * (k + one))) : Γ ⊢[PRAAx] φ := by
  refine .orE (lt_or_le y (k + one)) ?_ ?_
  · -- y < k + 1, so y ≤ k and y² ≤ k².
    have hy : (lt y (k + one) :: Γ) ⊢[PRAAx] le y k :=
      le_of_add_le_add_right (c := one) (le_congr (succ_eq_add_one y) (.eqRefl _) Prf.hyp0)
    exact le_lt_absurd φ (sq_le_sq hy) h₁.wk
  · exact le_lt_absurd φ (sq_le_sq Prf.hyp0) h₂.wk

end LeanProofs.IPRA
