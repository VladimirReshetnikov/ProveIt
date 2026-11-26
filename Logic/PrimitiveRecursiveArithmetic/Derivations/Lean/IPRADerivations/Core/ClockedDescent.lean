import IPRADerivations.Core.Descent
import IPRADerivations.Core.LinearCombination

/-!
# Clocked descent

Packet: `flt_ipra`, `sections/foundations.tex`, Lemma `lem:clocked`. For a quantifier-free predicate
`P(s)` on (coded) states and terms `D(s)`, `r(s)`, a derivation of
`P(s) → P(D(s)) ∧ r(D(s)) < r(s)` yields `∀ s ¬P(s)`.

The orbit `s_0 = s`, `s_{k+1} = D(s_k)` is the primitive recursion `orb`. For a state with `P(s)`
and `R = r(s)`, induction on `k` proves the quantifier-free invariant
`k ≤ R + 1 → P(s_k) ∧ r(s_k) + k ≤ R`; at `k = R + 1` it gives `R + 1 ≤ R`. No infinite sequence
and no least counterexample is used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.ClockedDescent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable (P : Fm PTm 1) (D r : PTm 1)

/-- `P(t)`. -/
def Pat {n : ℕ} (t : PTm n) : Fm PTm n := P.subst ![t]

/-- The orbit `orb(k, s) = D^k(s)`. -/
def iterF : PR 2 := rec2 (var 0) (Syn.subst ![var 1] D)

/-- `D^k(s)`. -/
abbrev orb {n : ℕ} (k s : PTm n) : PTm n := ap2 (iterF D) k s

variable {P D r}

@[simp] theorem subst_Pat {n m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    (Pat P t).subst σ = Pat P (Syn.subst σ t) := by
  simp only [Pat, Fm.subst_subst]
  congr 1; funext j; fin_cases j; rfl

omit P in
theorem subst_QF' {n m : ℕ} {φ : Fm PTm n} (h : φ.QF) (σ : Fin n → PTm m) : (φ.subst σ).QF := by
  induction φ generalizing m <;> simp_all [Fm.QF]

theorem Pat_QF (hP : P.QF) {n : ℕ} (t : PTm n) : (Pat P t).QF := subst_QF' hP _

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem Pat_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) (hp : Γ ⊢[PRAAx] Pat P a) : Γ ⊢[PRAAx] Pat P b :=
  Prf.eqSubst P ![a] ![b] (fun j => by fin_cases j; exact h) hp

theorem inst1_congr (β : PTm 1) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] inst1 β a ≐ inst1 β b :=
  Prf.eqCongr β fun j => by fin_cases j; exact h

theorem orb_zero (s : PTm n) : Γ ⊢[PRAAx] orb D zero s ≐ s := by
  have h := rec2_zero (Γ := Γ) (var 0) (Syn.subst ![var 1] D) s
  have e : Syn.subst ![s] (var 0 : PTm 1) = s := rfl
  rw [e] at h; exact h

theorem orb_succ (k s : PTm n) : Γ ⊢[PRAAx] orb D (succ k) s ≐ inst1 D (orb D k s) := by
  have h := rec2_succ (Γ := Γ) (var 0) (Syn.subst ![var 1] D) k s
  have e : Syn.subst ![k, ap2 (rec2 (var 0) (Syn.subst ![var 1] D)) k s, s] (Syn.subst ![var 1] D) =
      inst1 D (orb D k s) := by
    simp only [inst1, Syn.subst_subst]
    congr 1; funext j; fin_cases j; rfl
  rw [e] at h; exact h

/-- The step hypothesis at a state `t`. -/
theorem step_at (hstep : ([] : List (Fm PTm 1)) ⊢[PRAAx] P ⟶ (Pat P D ⋏ lt (inst1 r D) r)) (t : PTm n) :
    Γ ⊢[PRAAx] Pat P t ⟶ (Pat P (inst1 D t) ⋏ lt (inst1 r (inst1 D t)) (inst1 r t)) := by
  have h := inst (Γ := Γ) hstep ![t]
  have e₁ : P.subst ![t] = Pat P t := rfl
  simp only [Fm.subst_imp, Fm.subst_and, subst_Pat, subst_lt, e₁] at h
  have e₂ : Syn.subst ![t] D = inst1 D t := rfl
  have e₃ : ∀ u : PTm 1, Syn.subst ![t] (inst1 r u) = inst1 r (Syn.subst ![t] u) := fun u => by
    simp only [inst1, Syn.subst_subst]; congr 1; funext j; fin_cases j; rfl
  have e₄ : Syn.subst ![t] r = inst1 r t := rfl
  rw [e₃, e₂, e₄] at h
  exact h

/-- The invariant step. -/
theorem inv_step (hstep : ([] : List (Fm PTm 1)) ⊢[PRAAx] P ⟶ (Pat P D ⋏ lt (inst1 r D) r)) {k s R : PTm n}
    (ih : Γ ⊢[PRAAx] Pat P (orb D k s) ⋏ le (inst1 r (orb D k s) + k) R) :
    Γ ⊢[PRAAx] Pat P (orb D (succ k) s) ⋏ le (inst1 r (orb D (succ k) s) + succ k) R := by
  have st := Prf.impE (step_at hstep (orb D k s)) (Prf.andE₁ ih)
  have e := orb_succ (Γ := Γ) (D := D) k s
  refine .andI (Pat_congr e.eqSymm (Prf.andE₁ st)) ?_
  have lt' : Γ ⊢[PRAAx] lt (inst1 r (orb D (succ k) s)) (inst1 r (orb D k s)) :=
    le_congr (congrSucc (inst1_congr r e).eqSymm) (.eqRefl _) (Prf.andE₂ st)
  have l : Γ ⊢[PRAAx] le (inst1 r (orb D (succ k) s) + succ k) (inst1 r (orb D k s) + k) :=
    le_of_eq_add (d := monus (inst1 r (orb D k s)) (succ (inst1 r (orb D (succ k) s)))) (by
      ipra_lc natEq (eq_add_of_le lt'))
  exact le_trans l (Prf.andE₂ ih)

theorem subst_orb {m : ℕ} (σ : Fin n → PTm m) (k s : PTm n) :
    Syn.subst σ (orb D k s) = orb D (Syn.subst σ k) (Syn.subst σ s) := by simp [orb]

/-- The invariant; variables `0 = k`, `1 = s`. -/
private def invF (P : Fm PTm 1) (D r : PTm 1) : Fm PTm 2 :=
  Pat P (var 1) ⟶ (Pat P (orb D (var 0) (var 1)) ⋏ le (inst1 r (orb D (var 0) (var 1)) + var 0) (inst1 r (var 1)))

private theorem inv₀ (hP : P.QF) (hstep : ([] : List (Fm PTm 1)) ⊢[PRAAx] P ⟶ (Pat P D ⋏ lt (inst1 r D) r)) :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] invF P D r := by
  ipra_ind (⟨Pat_QF hP _, Pat_QF hP _, le_QF _ _⟩) [invF, subst_Pat, subst_le, subst_orb, subst_inst1]
  · refine .impI (.andI (Pat_congr (orb_zero _).eqSymm Prf.hyp0) ?_)
    exact le_congr ((inst1_congr r (orb_zero _)).eqSymm.eqTrans (add_zero _).eqSymm) (.eqRefl _) (le_refl _)
  · exact .impI (inv_step hstep (Prf.impE Prf.hyp1 Prf.hyp0))

/-- `lem:clocked`: no state satisfies `P`. -/
theorem clocked_at (hP : P.QF) (hstep : ([] : List (Fm PTm 1)) ⊢[PRAAx] P ⟶ (Pat P D ⋏ lt (inst1 r D) r))
    (s : PTm n) : Γ ⊢[PRAAx] neg (Pat P s) := by
  have i := inst (Γ := Γ) (inv₀ hP hstep) ![succ (inst1 r s), s]
  simp only [invF, Fm.subst_imp, Fm.subst_and, subst_Pat, subst_le, subst_orb, subst_inst1, PTm.subst_add,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at i
  refine .impI ?_
  have c := Prf.andE₂ (Prf.impE i.wk Prf.hyp0)
  exact lt_irrefl (inst1 r s) _ (le_trans (le_of_eq_add (d := inst1 r (orb D (succ (inst1 r s)) s))
    (by ipra_ring)) c)

theorem Pat_var (P : Fm PTm 1) : Pat P (var 0 : PTm 1) = P := by
  simp only [Pat]
  have : (![var 0] : Fin 1 → PTm 1) = var := by funext j; fin_cases j; rfl
  rw [this, Fm.subst_id]

/-- `lem:clocked`, closed: `∀ s ¬P(s)`. -/
theorem clocked (hP : P.QF) (hstep : ([] : List (Fm PTm 1)) ⊢[PRAAx] P ⟶ (Pat P D ⋏ lt (inst1 r D) r)) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (neg P) := by
  refine closeUniv 1 ?_
  have h := clocked_at (Γ := ([] : List (Fm PTm 1))) hP hstep (var 0)
  rwa [Pat_var] at h

end LeanProofs.IPRA.ClockedDescent
