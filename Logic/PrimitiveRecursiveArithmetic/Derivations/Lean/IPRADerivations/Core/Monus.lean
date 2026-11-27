import IPRADerivations.Core.Sums

/-!
# Truncated subtraction in iPRA

The laws of `a ∸ b` (`PTm.monus`), each derived by quantifier-free induction:

* `zero_or_succ`: `a = 0 ∨ a = S (pred a)`;
* `zero_monus`: `0 ∸ b = 0`; `succ_monus_succ`: `S a ∸ S b = a ∸ b`; `monus_self`: `a ∸ a = 0`;
* `add_monus`: `(a + b) ∸ b = a`; `monus_add`: `a ∸ (a + c) = 0`;
* the key pair, proved by one joint induction:
  `monus_max`: `(a ∸ b) + b = (b ∸ a) + a` and `monus_mul`: `(a ∸ b)(b ∸ a) = 0`.

They are the base of the order relation `a ≤ b :⇔ a ∸ b = 0` in `Core.Order`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Substitution normal forms for formulas of `+`, `*`, `S`, `pred` and `∸`. -/
macro "ipra_subst'" : tactic =>
  `(tactic| simp only [Fm.subst_eq, Fm.subst_imp, Fm.subst_and, Fm.subst_or, Fm.subst_bot,
      PTm.subst_add, PTm.subst_mul, PTm.subst_pred, PTm.subst_monus, Syn.subst_var,
      Syn.inst_zero, Syn.inst_succ, Syn.repl_zero, Syn.repl_succ, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ, inst_two, repl_one, repl_two])

/-! ## Zero or successor -/

private abbrev zosF : Fm PTm 1 := (var 0 ≐ zero) ⋎ (var 0 ≐ succ (pred (var 0)))

private theorem zero_or_succ₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] zosF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · ipra_subst'; exact .orI₁ (.eqRefl _)
  · ipra_subst'; exact .orI₂ (congrSucc (pred_succ _).eqSymm)

theorem zero_or_succ (a : PTm n) : Γ ⊢[PRAAx] (a ≐ zero) ⋎ (a ≐ succ (pred a)) := by
  simpa using inst (Γ := Γ) zero_or_succ₀ ![a]

/-- A successor is not zero, as an elimination rule. -/
theorem succ_ne_zero' {a : PTm n} (φ : Fm PTm n) (h : Γ ⊢[PRAAx] succ a ≐ zero) : Γ ⊢[PRAAx] φ :=
  .botE φ (succ_ne_zero h)

/-! ## Basic laws -/

private abbrev zmF : Fm PTm 1 := monus zero (var 0) ≐ zero

private theorem zero_monus₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] zmF := by
  refine ind _ trivial ?_ ?_
  · ipra_subst'; exact monus_zero _
  · ipra_subst'
    exact (monus_succ _ _).eqTrans ((congrPred Prf.hyp0).eqTrans pred_zero)

theorem zero_monus (b : PTm n) : Γ ⊢[PRAAx] monus zero b ≐ zero := by
  simpa using inst (Γ := Γ) zero_monus₀ ![b]

/-- Variables: `0 = b` (induction), `1 = a`. -/
private abbrev smsF : Fm PTm 2 := monus (succ (var 1)) (succ (var 0)) ≐ monus (var 1) (var 0)

private theorem succ_monus_succ₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] smsF := by
  refine ind _ trivial ?_ ?_
  · ipra_subst'
    exact (monus_succ _ _).eqTrans <| (congrPred (monus_zero _)).eqTrans <|
      (pred_succ _).eqTrans (monus_zero _).eqSymm
  · ipra_subst'
    exact (monus_succ _ _).eqTrans <| (congrPred Prf.hyp0).eqTrans (monus_succ _ _).eqSymm

theorem succ_monus_succ (a b : PTm n) : Γ ⊢[PRAAx] monus (succ a) (succ b) ≐ monus a b := by
  simpa using inst (Γ := Γ) succ_monus_succ₀ ![b, a]

private abbrev mselfF : Fm PTm 1 := monus (var 0) (var 0) ≐ zero

private theorem monus_self₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] mselfF := by
  refine ind _ trivial ?_ ?_
  · ipra_subst'; exact monus_zero _
  · ipra_subst'; exact (succ_monus_succ _ _).eqTrans Prf.hyp0

theorem monus_self (a : PTm n) : Γ ⊢[PRAAx] monus a a ≐ zero := by
  simpa using inst (Γ := Γ) monus_self₀ ![a]

/-- Variables: `0 = b` (induction), `1 = a`. -/
private abbrev amF : Fm PTm 2 := monus (var 1 + var 0) (var 0) ≐ var 1

private theorem add_monus₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] amF := by
  refine ind _ trivial ?_ ?_
  · ipra_subst'; exact (monus_zero _).eqTrans (add_zero _)
  · ipra_subst'
    exact (congrMonus (add_succ _ _) (.eqRefl _)).eqTrans <|
      (succ_monus_succ _ _).eqTrans Prf.hyp0

theorem add_monus (a b : PTm n) : Γ ⊢[PRAAx] monus (a + b) b ≐ a := by
  simpa using inst (Γ := Γ) add_monus₀ ![b, a]

theorem add_monus' (a b : PTm n) : Γ ⊢[PRAAx] monus (b + a) b ≐ a :=
  (congrMonus (add_comm _ _) (.eqRefl _)).eqTrans (add_monus a b)

/-- Variables: `0 = a` (induction), `1 = c`. -/
private abbrev maF : Fm PTm 2 := monus (var 0) (var 0 + var 1) ≐ zero

private theorem monus_add₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] maF := by
  refine ind _ trivial ?_ ?_
  · ipra_subst'; exact zero_monus _
  · ipra_subst'
    exact (congrMonus (.eqRefl _) (succ_add _ _)).eqTrans <|
      (succ_monus_succ _ _).eqTrans Prf.hyp0

theorem monus_add (a c : PTm n) : Γ ⊢[PRAAx] monus a (a + c) ≐ zero := by
  simpa using inst (Γ := Γ) monus_add₀ ![a, c]

/-! ## The joint induction -/

/-- `(a ∸ b) + b = (b ∸ a) + a ∧ (a ∸ b)(b ∸ a) = 0`; variables `0 = b`, `1 = a`. -/
private abbrev mmF : Fm PTm 2 :=
  (monus (var 1) (var 0) + var 0 ≐ monus (var 0) (var 1) + var 1) ⋏
    (monus (var 1) (var 0) * monus (var 0) (var 1) ≐ zero)

/-- If `S c · d = 0` then `d = 0`. -/
theorem eq_zero_of_succ_mul {c d : PTm n} (h : Γ ⊢[PRAAx] succ c * d ≐ zero) :
    Γ ⊢[PRAAx] d ≐ zero := by
  refine .orE (zero_or_succ d) Prf.hyp0 ?_
  have e : (d ≐ succ (pred d)) :: Γ ⊢[PRAAx] succ (succ c * pred d + c) ≐ zero :=
    ((add_succ _ _).eqSymm.eqTrans (mul_succ _ _).eqSymm).eqTrans
      ((congrMul (.eqRefl _) Prf.hyp0).eqSymm.eqTrans h.wk)
  exact succ_ne_zero' _ e

/-- The contexts of the two cases of the induction step. -/
private abbrev ΔA : List (Fm PTm 2) := (monus (var 1) (var 0) ≐ zero) :: [mmF]
private abbrev ΔB : List (Fm PTm 2) :=
  (monus (var 1) (var 0) ≐ succ (pred (monus (var 1) (var 0)))) :: [mmF]

private theorem monus_maxmul₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] mmF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · ipra_subst'
    refine .andI ?_ ?_
    · exact (add_zero _).eqTrans <| (monus_zero _).eqTrans <|
        ((congrAdd (zero_monus _) (.eqRefl _)).eqTrans (zero_add _)).eqSymm
    · exact mul_eq_zero_of_right (zero_monus _)
  · ipra_subst'
    -- context: [mmF]; write X = a ∸ b, Y = b ∸ a
    have hM : [mmF] ⊢[PRAAx] monus (var 1) (var 0) + var 0 ≐ monus (var 0) (var 1) + var 1 :=
      .andE₁ Prf.hyp0
    have hP : [mmF] ⊢[PRAAx] monus (var 1) (var 0) * monus (var 0) (var 1) ≐ zero :=
      .andE₂ Prf.hyp0
    refine .orE (zero_or_succ (monus (var 1) (var 0))) ?_ ?_
    · -- Case X = 0.
      have hX : (ΔA : List (Fm PTm 2)) ⊢[PRAAx] monus (var 1) (var 0) ≐ zero := Prf.hyp0
      have hX' : (ΔA : List (Fm PTm 2)) ⊢[PRAAx] monus (var 1) (succ (var 0)) ≐ zero :=
        (monus_succ _ _).eqTrans ((congrPred hX).eqTrans pred_zero)
      -- b = Y + a
      have hb : (ΔA : List (Fm PTm 2)) ⊢[PRAAx] var 0 ≐ monus (var 0) (var 1) + var 1 :=
        (zero_add _).eqSymm.eqTrans ((congrAdd hX (.eqRefl _)).eqSymm.eqTrans hM.wk)
      -- S b ∸ a = S Y
      have hY' : (ΔA : List (Fm PTm 2)) ⊢[PRAAx] monus (succ (var 0)) (var 1) ≐ succ (monus (var 0) (var 1)) :=
        (congrMonus ((congrSucc hb).eqTrans (succ_add _ _).eqSymm) (.eqRefl _)).eqTrans
          (add_monus _ _)
      refine .andI ?_ ?_
      · refine (congrAdd hX' (.eqRefl _)).eqTrans <| (zero_add _).eqTrans ?_
        refine .eqTrans ?_ (congrAdd hY' (.eqRefl _)).eqSymm
        exact (congrSucc hb).eqTrans (succ_add _ _).eqSymm
      · exact mul_eq_zero_of_left hX'
    · -- Case X = S c with c = pred X.
      have hX : (ΔB : List (Fm PTm 2)) ⊢[PRAAx] monus (var 1) (var 0) ≐ succ (pred (monus (var 1) (var 0))) := Prf.hyp0
      have hX' : (ΔB : List (Fm PTm 2)) ⊢[PRAAx] monus (var 1) (succ (var 0)) ≐ pred (monus (var 1) (var 0)) :=
        (monus_succ _ _).eqTrans ((congrPred hX).eqTrans (pred_succ _))
      -- Y = 0 from S c · Y = 0
      have hY : (ΔB : List (Fm PTm 2)) ⊢[PRAAx] monus (var 0) (var 1) ≐ zero :=
        eq_zero_of_succ_mul ((congrMul hX (.eqRefl _)).eqSymm.eqTrans hP.wk)
      -- a = S (c + b)
      have ha : (ΔB : List (Fm PTm 2)) ⊢[PRAAx] var 1 ≐ succ (pred (monus (var 1) (var 0)) + var 0) := by
        refine (zero_add _).eqSymm.eqTrans ?_
        refine (congrAdd hY (.eqRefl _)).eqSymm.eqTrans ?_
        refine hM.wk.eqSymm.eqTrans ?_
        exact (congrAdd hX (.eqRefl _)).eqTrans (succ_add _ _)
      -- S b ∸ a = 0
      have hY' : (ΔB : List (Fm PTm 2)) ⊢[PRAAx] monus (succ (var 0)) (var 1) ≐ zero := by
        refine (congrMonus (.eqRefl _) ha).eqTrans ?_
        refine (succ_monus_succ _ _).eqTrans ?_
        exact (congrMonus (.eqRefl _) (add_comm _ _)).eqTrans (monus_add _ _)
      refine .andI ?_ ?_
      · refine (congrAdd hX' (.eqRefl _)).eqTrans <| (add_succ _ _).eqTrans ?_
        refine .eqTrans ?_ ((congrAdd hY' (.eqRefl _)).eqTrans (zero_add _)).eqSymm
        exact ha.eqSymm
      · exact mul_eq_zero_of_right hY'

theorem monus_max (a b : PTm n) : Γ ⊢[PRAAx] monus a b + b ≐ monus b a + a := by
  have h := inst (Γ := Γ) monus_maxmul₀ (![b, a] : Fin 2 → PTm n)
  simp at h
  exact .andE₁ h

theorem monus_mul (a b : PTm n) : Γ ⊢[PRAAx] monus a b * monus b a ≐ zero := by
  have h := inst (Γ := Γ) monus_maxmul₀ (![b, a] : Fin 2 → PTm n)
  simp at h
  exact .andE₂ h

end LeanProofs.IPRA
