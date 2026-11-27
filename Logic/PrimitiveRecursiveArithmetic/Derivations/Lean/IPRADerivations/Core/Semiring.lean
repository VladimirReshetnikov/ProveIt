import IPRADerivations.Core.Basic

set_option linter.unusedSimpArgs false

/-!
# The commutative semiring laws in iPRA

Each law is first derived as an open theorem of `Prf PRAAx` over its own free
variables, by quantifier-free induction on variable `0` (`ind`), and then
instantiated at arbitrary terms under arbitrary hypotheses (`inst`).

The laws derived are those of a commutative semiring for `+`, `*`, `0` and
`1 = S 0`, together with additive cancellation and the injectivity and
non-vanishing of the successor, all at arbitrary terms.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Successor axioms at arbitrary terms -/

theorem succ_inj {a b : PTm n} (h : Γ ⊢[PRAAx] succ a ≐ succ b) : Γ ⊢[PRAAx] a ≐ b := by
  have ax := Prf.ax (Γ := Γ) PRAAx.succInj ![a, b]
  simp only [Fm.subst_imp, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, Syn.subst_var] at ax
  exact .impE ax h

theorem succ_ne_zero {a : PTm n} (h : Γ ⊢[PRAAx] succ a ≐ zero) : Γ ⊢[PRAAx] Fm.bot :=
  .impE (PRA.succNeZero a) h

/-! ## Addition -/

private theorem add_zero₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] var 0 + zero ≐ var 0 := by
  refine ind _ trivial ?_ ?_
  · simpa using zero_add (Γ := []) zero
  · simpa using (succ_add (Γ := [_]) (var 0) zero).eqTrans (congrSucc Prf.hyp0)

theorem add_zero (a : PTm n) : Γ ⊢[PRAAx] a + zero ≐ a := by
  simpa using inst (Γ := Γ) add_zero₀ ![a]

private theorem add_succ₀ :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] var 0 + succ (var 1) ≐ succ (var 0 + var 1) := by
  refine ind _ trivial ?_ ?_
  · simpa using (zero_add (Γ := []) (succ (var 0))).eqTrans
      (congrSucc (zero_add (var 0))).eqSymm
  · simp only [Fm.subst_eq, PTm.subst_add, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Syn.repl_zero, Syn.repl_succ]
    refine (succ_add _ _).eqTrans ?_
    refine (congrSucc (by simpa using Prf.hyp0)).eqTrans ?_
    exact (congrSucc (succ_add _ _)).eqSymm

theorem add_succ (a b : PTm n) : Γ ⊢[PRAAx] a + succ b ≐ succ (a + b) := by
  simpa using inst (Γ := Γ) add_succ₀ ![a, b]

private theorem add_comm₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] var 0 + var 1 ≐ var 1 + var 0 := by
  refine ind _ trivial ?_ ?_
  · simpa using (zero_add (Γ := []) (var 0)).eqTrans (add_zero (var 0)).eqSymm
  · simp only [Fm.subst_eq, PTm.subst_add, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Syn.repl_zero, Syn.repl_succ]
    refine (succ_add _ _).eqTrans ?_
    refine (congrSucc (by simpa using Prf.hyp0)).eqTrans ?_
    exact (add_succ _ _).eqSymm

theorem add_comm (a b : PTm n) : Γ ⊢[PRAAx] a + b ≐ b + a := by
  simpa using inst (Γ := Γ) add_comm₀ ![a, b]

private theorem add_assoc₀ :
    ([] : List (Fm PTm 3)) ⊢[PRAAx] var 0 + var 1 + var 2 ≐ var 0 + (var 1 + var 2) := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.inst_succ]
    exact (congrAdd (zero_add _) (.eqRefl _)).eqTrans (zero_add _).eqSymm
  · simp only [Fm.subst_eq, PTm.subst_add, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Syn.repl_zero, Syn.repl_succ]
    refine (congrAdd (succ_add _ _) (.eqRefl _)).eqTrans ?_
    refine (succ_add _ _).eqTrans ?_
    refine (congrSucc (by simpa using Prf.hyp0)).eqTrans ?_
    exact (succ_add _ _).eqSymm

theorem add_assoc (a b c : PTm n) : Γ ⊢[PRAAx] a + b + c ≐ a + (b + c) := by
  simpa using inst (Γ := Γ) add_assoc₀ ![a, b, c]

theorem add_right_comm (a b c : PTm n) : Γ ⊢[PRAAx] a + b + c ≐ a + c + b :=
  (add_assoc a b c).eqTrans <| (congrAdd (.eqRefl a) (add_comm b c)).eqTrans
    (add_assoc a c b).eqSymm

/-! ## Multiplication -/

private theorem mul_zero₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] var 0 * zero ≐ zero := by
  refine ind _ trivial ?_ ?_
  · simpa using zero_mul (Γ := []) zero
  · simp only [Fm.subst_eq, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Syn.repl_zero, ConciseIPRA.PTm.subst_zero]
    exact (succ_mul _ _).eqTrans <| (add_zero _).eqTrans Prf.hyp0

theorem mul_zero (a : PTm n) : Γ ⊢[PRAAx] a * zero ≐ zero := by
  simpa using inst (Γ := Γ) mul_zero₀ ![a]

/-- A product is zero when its left factor is zero. -/
theorem mul_eq_zero_of_left {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ zero) : Γ ⊢[PRAAx] a * b ≐ zero :=
  (congrMul h (.eqRefl b)).eqTrans (zero_mul b)

/-- A product is zero when its right factor is zero. -/
theorem mul_eq_zero_of_right {a b : PTm n} (h : Γ ⊢[PRAAx] b ≐ zero) : Γ ⊢[PRAAx] a * b ≐ zero :=
  (congrMul (.eqRefl a) h).eqTrans (mul_zero a)

private theorem mul_succ₀ :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] var 0 * succ (var 1) ≐ var 0 * var 1 + var 0 := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_mul, PTm.subst_add, ConciseIPRA.PTm.subst_succ,
      Syn.subst_var, Syn.inst_zero, Syn.inst_succ]
    exact (zero_mul _).eqTrans <| ((add_zero _).eqTrans (zero_mul _)).eqSymm
  · simp only [Fm.subst_eq, PTm.subst_mul, PTm.subst_add, ConciseIPRA.PTm.subst_succ,
      Syn.subst_var, Syn.repl_zero, Syn.repl_succ]
    -- S v0 * S v1 = v0 * S v1 + S v1 = (v0 v1 + v0) + S v1 = S ((v0 v1 + v0) + v1)
    refine (succ_mul _ _).eqTrans ?_
    refine (congrAdd (by simpa using Prf.hyp0) (.eqRefl _)).eqTrans ?_
    refine (add_succ _ _).eqTrans ?_
    refine (congrSucc (add_right_comm _ _ _)).eqTrans ?_
    refine (add_succ _ _).eqSymm.eqTrans ?_
    exact congrAdd (succ_mul _ _).eqSymm (.eqRefl _)

theorem mul_succ (a b : PTm n) : Γ ⊢[PRAAx] a * succ b ≐ a * b + a := by
  simpa using inst (Γ := Γ) mul_succ₀ ![a, b]

private theorem mul_comm₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] var 0 * var 1 ≐ var 1 * var 0 := by
  refine ind _ trivial ?_ ?_
  · simpa using (zero_mul (Γ := []) (var 0)).eqTrans (mul_zero (var 0)).eqSymm
  · simp only [Fm.subst_eq, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Syn.repl_zero, Syn.repl_succ]
    refine (succ_mul _ _).eqTrans ?_
    refine (congrAdd (by simpa using Prf.hyp0) (.eqRefl _)).eqTrans ?_
    exact (mul_succ _ _).eqSymm

theorem mul_comm (a b : PTm n) : Γ ⊢[PRAAx] a * b ≐ b * a := by
  simpa using inst (Γ := Γ) mul_comm₀ ![a, b]

private theorem add_mul₀ :
    ([] : List (Fm PTm 3)) ⊢[PRAAx] (var 0 + var 1) * var 2 ≐ var 0 * var 2 + var 1 * var 2 := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
      Syn.inst_succ]
    refine (congrMul (zero_add _) (.eqRefl _)).eqTrans ?_
    exact ((congrAdd (zero_mul _) (.eqRefl _)).eqTrans (zero_add _)).eqSymm
  · simp only [Fm.subst_eq, PTm.subst_mul, PTm.subst_add, ConciseIPRA.PTm.subst_succ,
      Syn.subst_var, Syn.repl_zero, Syn.repl_succ]
    refine (congrMul (succ_add _ _) (.eqRefl _)).eqTrans ?_
    refine (succ_mul _ _).eqTrans ?_
    refine (congrAdd (by simpa using Prf.hyp0) (.eqRefl _)).eqTrans ?_
    refine (add_right_comm _ _ _).eqTrans ?_
    exact congrAdd (succ_mul _ _).eqSymm (.eqRefl _)

theorem add_mul (a b c : PTm n) : Γ ⊢[PRAAx] (a + b) * c ≐ a * c + b * c := by
  simpa using inst (Γ := Γ) add_mul₀ ![a, b, c]

theorem mul_add (a b c : PTm n) : Γ ⊢[PRAAx] a * (b + c) ≐ a * b + a * c :=
  (mul_comm _ _).eqTrans <| (add_mul _ _ _).eqTrans (congrAdd (mul_comm _ _) (mul_comm _ _))

private theorem mul_assoc₀ :
    ([] : List (Fm PTm 3)) ⊢[PRAAx] var 0 * var 1 * var 2 ≐ var 0 * (var 1 * var 2) := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_succ]
    exact (congrMul (zero_mul _) (.eqRefl _)).eqTrans <| (zero_mul _).eqTrans (zero_mul _).eqSymm
  · simp only [Fm.subst_eq, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Syn.repl_zero, Syn.repl_succ]
    refine (congrMul (succ_mul _ _) (.eqRefl _)).eqTrans ?_
    refine (add_mul _ _ _).eqTrans ?_
    refine (congrAdd (by simpa using Prf.hyp0) (.eqRefl _)).eqTrans ?_
    exact (succ_mul _ _).eqSymm

theorem mul_assoc (a b c : PTm n) : Γ ⊢[PRAAx] a * b * c ≐ a * (b * c) := by
  simpa using inst (Γ := Γ) mul_assoc₀ ![a, b, c]

theorem one_mul (a : PTm n) : Γ ⊢[PRAAx] succ zero * a ≐ a :=
  (succ_mul _ _).eqTrans <| (congrAdd (zero_mul _) (.eqRefl _)).eqTrans (zero_add _)

theorem succ_eq_add_one (a : PTm n) : Γ ⊢[PRAAx] succ a ≐ a + succ zero :=
  (congrSucc (add_zero a)).eqSymm.eqTrans (add_succ _ _).eqSymm

/-! ## Additive cancellation -/

private theorem add_left_cancel₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx]
    (var 0 + var 1 ≐ var 0 + var 2) ⟶ (var 1 ≐ var 2) := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
      Syn.inst_succ]
    exact .impI <| (zero_add _).eqSymm.eqTrans <| Prf.hyp0.eqTrans (zero_add _)
  · simp only [Fm.subst_imp, Fm.subst_eq, PTm.subst_add, ConciseIPRA.PTm.subst_succ,
      Syn.subst_var, Syn.repl_zero, Syn.repl_succ]
    refine .impI (.impE (by simpa using Prf.hyp1) (succ_inj ?_))
    exact (succ_add _ _).eqSymm.eqTrans <| Prf.hyp0.eqTrans (succ_add _ _)

theorem add_left_cancel {a b c : PTm n} (h : Γ ⊢[PRAAx] a + b ≐ a + c) : Γ ⊢[PRAAx] b ≐ c := by
  have ax := inst (Γ := Γ) add_left_cancel₀ ![a, b, c]
  simp at ax
  exact .impE ax h

theorem add_right_cancel {a b c : PTm n} (h : Γ ⊢[PRAAx] a + c ≐ b + c) : Γ ⊢[PRAAx] a ≐ b :=
  add_left_cancel ((add_comm _ _).eqTrans (h.eqTrans (add_comm _ _)))

end LeanProofs.IPRA
