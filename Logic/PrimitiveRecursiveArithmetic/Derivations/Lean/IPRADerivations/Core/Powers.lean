import IPRADerivations.Core.Pairing

/-!
# Powers and squares in iPRA

With `pw a m = aᵐ` (the symbol `powF` of `Core.Definitions`):

* `pw_add`: `a^{m+k} = aᵐ aᵏ`;
* `pw_mul_bases`, `pw_pow`: `(ab)^m = a^m b^m` and `(a^e)^d = a^{ed}`;
* `pw_le_pw`: `a ≤ b → aᵐ ≤ bᵐ`;
* `pw_one_le`, `pw_le_pw_exp`: for a base at least one, powers stay at least one and increase with the exponent;
* `le_self_pw`: `S a ≤ (S a)^{S m}`;
* `pw_bernoulli`: the first two terms of a power of a sum give a lower bound;
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

/-- Evaluate a power whose base and exponent are both numerals. -/
theorem pw_numeral (a : ℕ) : (b : ℕ) → Γ ⊢[PRAAx] pw (num a : PTm n) (num b) ≐ num (a ^ b)
  | 0 => (pw_zero _).eqTrans (by apply deriveNat; ipra_simps; simp)
  | b + 1 => (pw_succ (num a) (num b)).eqTrans
      ((congrMul (pw_numeral a b) (.eqRefl _)).eqTrans (by apply deriveNat; ipra_simps; push_cast; ring))

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

/-- Evaluate the numeral factor in a power with a shifted exponent. -/
theorem pw_add_numeral (a b : ℕ) (e : PTm n) : Γ ⊢[PRAAx]
    pw (num a) (e + num b) ≐ pw (num a) e * num (a ^ b) :=
  (pw_add (num a) e (num b)).eqTrans (congrMul (.eqRefl _) (pw_numeral a b))

/-- Variables: `0 = m`, `1 = a`, `2 = b`. -/
private abbrev pwMulBasesF : Fm PTm 3 :=
  pw (var 1 * var 2) (var 0) ≐ pw (var 1) (var 0) * pw (var 2) (var 0)

private theorem pw_mul_bases₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] pwMulBasesF := by
  refine ind _ trivial ?_ ?_
  · pw_subst
    exact (pw_zero _).eqTrans ((congrMul (pw_zero _) (pw_zero _)).eqTrans (one_mul one)).eqSymm
  · pw_subst
    refine withEq Prf.hyp0 fun ih => withEq (pw_succ (var 1 * var 2) (var 0)) fun product =>
      withEq (pw_succ (var 1) (var 0)) fun left => withEq (pw_succ (var 2) (var 0)) fun right => ?_
    apply deriveNat; ipra_simps; rw [product, left, right, ih]; ring

/-- The power of a product is the product of the powers. -/
theorem pw_mul_bases (a b m : PTm n) : Γ ⊢[PRAAx] pw (a * b) m ≐ pw a m * pw b m := by
  simpa using inst (Γ := Γ) pw_mul_bases₀ (![m, a, b] : Fin 3 → PTm n)

/-- Variables: `0 = d`, `1 = a`, `2 = e`. -/
private abbrev pwPowF : Fm PTm 3 := pw (pw (var 1) (var 2)) (var 0) ≐ pw (var 1) (var 2 * var 0)

private theorem pw_pow₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] pwPowF := by
  refine ind _ trivial ?_ ?_
  · pw_subst
    exact (pw_zero _).eqTrans ((congrAp2 powF (mul_zero _) (.eqRefl _)).eqTrans (pw_zero _)).eqSymm
  · pw_subst
    refine (pw_succ _ _).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans ?_)
    exact (pw_add _ _ _).eqSymm.eqTrans (congrAp2 powF (mul_succ _ _).eqSymm (.eqRefl _))

/-- Iterated powers multiply their exponents. -/
theorem pw_pow (a e d : PTm n) : Γ ⊢[PRAAx] pw (pw a e) d ≐ pw a (e * d) := by
  simpa using inst (Γ := Γ) pw_pow₀ (![d, a, e] : Fin 3 → PTm n)

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

/-! ## Homogeneous Bernoulli inequality -/

theorem pw_bernoulli_base (a b : PTm n) :
    Γ ⊢[PRAAx] le (pw a (succ zero) + succ zero * pw a zero * b) (pw (a + b) (succ zero)) := by
  refine le_of_eq_add (d := zero) ?_
  have ha := natEq (pw_one (Γ := Γ) a)
  have hb := natEq (pw_one (Γ := Γ) (a + b))
  have h0 := natEq (pw_zero (Γ := Γ) a)
  apply deriveNat
  ipra_simps
  rw [ha, hb, h0]
  ring

theorem pw_bernoulli_step {a b m : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw a (succ m) + succ m * pw a m * b) (pw (a + b) (succ m))) :
    Γ ⊢[PRAAx] le (pw a (succ (succ m)) + succ (succ m) * pw a (succ m) * b) (pw (a + b) (succ (succ m))) := by
  refine le_trans (le_of_eq_add (d := succ m * pw a m * b * b) ?_)
    (le_congr (.eqRefl _) (pw_succ (a + b) (succ m)).eqSymm (mul_le_mul_right (a + b) ih))
  have h₁ := natEq (pw_succ (Γ := Γ) a m)
  have h₂ := natEq (pw_succ (Γ := Γ) a (succ m))
  apply deriveNat
  ipra_simps
  rw [h₂, h₁]
  ring

private abbrev pwBernoulliF : Fm PTm 3 :=
  le (pw (var 1) (succ (var 0)) + succ (var 0) * pw (var 1) (var 0) * var 2)
    (pw (var 1 + var 2) (succ (var 0)))

private theorem pw_bernoulli₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] pwBernoulliF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · pw_subst
    exact pw_bernoulli_base _ _
  · pw_subst
    exact pw_bernoulli_step Prf.hyp0

/-- Homogeneous Bernoulli inequality, at every encoded successor exponent. -/
theorem pw_bernoulli (a b m : PTm n) :
    Γ ⊢[PRAAx] le (pw a (succ m) + succ m * pw a m * b) (pw (a + b) (succ m)) := by
  simpa using inst (Γ := Γ) pw_bernoulli₀ (![m, a, b] : Fin 3 → PTm n)

/-- Homogeneous Bernoulli with increment one. -/
theorem pw_bernoulli_unit (a m : PTm n) :
    Γ ⊢[PRAAx] le (pw a (succ m) + succ m * pw a m) (pw (succ a) (succ m)) :=
  le_congr (by ipra_ring) (congrAp2 powF (.eqRefl _) (succ_eq_add_one a).eqSymm)
    (pw_bernoulli a one m)

/-- The ratio a/(a+1), raised to a+1, is at most one half after clearing denominators. -/
theorem pw_bernoulli_half (a : PTm n) :
    Γ ⊢[PRAAx] le (num 2 * pw a (succ a)) (pw (succ a) (succ a)) := by
  refine le_trans (le_of_eq_add (d := pw a a) ?_) (pw_bernoulli_unit a a)
  have h := natEq (pw_succ (Γ := Γ) a a)
  apply deriveNat
  ipra_simps
  rw [h]
  ring

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
