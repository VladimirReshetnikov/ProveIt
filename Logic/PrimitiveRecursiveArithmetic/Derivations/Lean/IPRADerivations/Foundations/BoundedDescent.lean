import IPRADerivations.Foundations.IterationFusion
import IPRADerivations.Foundations.BoundedReflection

/-!
# Bounded descent with a rank (`ipra_coherent_methods_2026-11-15`, `thm:rank`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, Theorem `thm:rank` ("Bounded descent
with a reconstruction invariant").

The data are unary terms: a transition `T`, a rank `r`, a terminal test `D` (terminal when
`D(s) = 1`) and a validity bit `V` (valid when `V(s) = 1`). The hypotheses (`Descent`) are
the three clauses of the theorem, as rules at arbitrary terms and contexts:

* `T` preserves validity;
* `T` fixes terminal valid states;
* `V(s) = 1` and `D(s) ≠ 1` give `r(T(s)) < r(s)`.

Then, for a valid `s₀`:

* `descent_inv`: for every `t`, `V(T^t s₀) = 1` and `D(T^t s₀) = 1 ∨ r(T^t s₀) + t ≤ r(s₀)`
  (the packet's induction formula, quantifier-free);
* `terminal`: `D(T^{r(s₀)} s₀) = 1`: the iterate `T^{r(s₀)}(s₀)` is terminal; closed form
  `terminal_closed`.

`T^t` is `iter` of `Foundations/IterationFusion`. The clause "every bounded invariant
preserved by `T` holds there" is `simulation` of that module.

Instance with every hypothesis discharged: counting down by the predecessor,
`pred^{s₀}(s₀) = 0` (`countdown_closed`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.BoundedDescent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.IterationFusion
open LeanProofs.IPRA.Foundations.BoundedReflection (eq_of_eqb one_ne_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The hypotheses of `thm:rank`. -/
structure Descent (T r D V : PTm 1) : Prop where
  pres : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] app1 V (app1 T s) ≐ one)
  fix : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] app1 D s ≐ one) → (Γ ⊢[PRAAx] app1 T s ≐ s)
  dec : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {s : PTm k},
    (Γ ⊢[PRAAx] app1 V s ≐ one) → (Γ ⊢[PRAAx] neg (app1 D s ≐ one)) →
      (Γ ⊢[PRAAx] lt (app1 r (app1 T s)) (app1 r s))

section Rank

variable {T r D V : PTm 1}

/-- One step of the invariant. -/
theorem inv_step (H : Descent T r D V) {t s₀ : PTm k}
    (hv : Γ ⊢[PRAAx] app1 V (iter T t s₀) ≐ one)
    (hd : Γ ⊢[PRAAx] (app1 D (iter T t s₀) ≐ one) ⋎
      le (app1 r (iter T t s₀) + t) (app1 r s₀)) :
    Γ ⊢[PRAAx] (app1 V (iter T (succ t) s₀) ≐ one) ⋏
      ((app1 D (iter T (succ t) s₀) ≐ one) ⋎
        le (app1 r (iter T (succ t) s₀) + succ t) (app1 r s₀)) := by
  have cs := iter_succ (Γ := Γ) T t s₀
  refine .andI ((congrApp1 V cs).eqTrans (H.pres hv)) ?_
  refine .orE (eq_or_ne (app1 D (iter T t s₀)) one) ?_ ?_
  · -- terminal already: the state does not move
    have hfix := H.fix hv.wk (Prf.hyp0 (Γ := Γ) (φ := app1 D (iter T t s₀) ≐ one))
    exact .orI₁ ((congrApp1 D (cs.wk.eqTrans hfix)).eqTrans Prf.hyp0)
  · refine .orE hd.wk (.botE _ (.impE Prf.hyp1 Prf.hyp0)) ?_
    -- not terminal: the rank drops by at least one
    have hdec := H.dec (hv.wk (ψ := neg (app1 D (iter T t s₀) ≐ one))).wk
      (Prf.hyp1 (Γ := Γ) (φ := neg (app1 D (iter T t s₀) ≐ one))
        (ψ := le (app1 r (iter T t s₀) + t) (app1 r s₀)))
    have e₁ := natEq (eq_add_of_le hdec)
    have e₂ := natEq (eq_add_of_le (Prf.hyp0 (Γ := neg (app1 D (iter T t s₀) ≐ one) :: Γ)
      (φ := le (app1 r (iter T t s₀) + t) (app1 r s₀))))
    have e₃ := natEq (congrApp1 r ((cs.wk (ψ := neg (app1 D (iter T t s₀) ≐ one))).wk
      (ψ := le (app1 r (iter T t s₀) + t) (app1 r s₀))))
    refine .orI₂ (le_of_eq_add (d := monus (app1 r (iter T t s₀))
      (succ (app1 r (app1 T (iter T t s₀)))) +
      monus (app1 r s₀) (app1 r (iter T t s₀) + t)) ?_)
    apply deriveNat; ipra_simps
    linear_combination e₂ + e₁ - e₃

/-- Variables: `0 = t`, `1 = s₀`. -/
private def invF (T r D V : PTm 1) : Fm PTm 2 :=
  (app1 V (var 1) ≐ one) ⟶
    ((app1 V (iter T (var 0) (var 1)) ≐ one) ⋏
      ((app1 D (iter T (var 0) (var 1)) ≐ one) ⋎
        le (app1 r (iter T (var 0) (var 1)) + var 0) (app1 r (var 1))))

private theorem inv₀ (H : Descent T r D V) : ([] : List (Fm PTm 2)) ⊢[PRAAx] invF T r D V := by
  refine ind _ ⟨trivial, trivial, trivial, trivial⟩ ?_ ?_
  · simp only [invF, Fm.subst_imp, Fm.subst_and, Fm.subst_or, Fm.subst_eq, subst_le, subst_app1,
      subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI (.andI ((congrApp1 V (iter_zero T _)).eqTrans Prf.hyp0) (.orI₂ ?_))
    exact le_congr ((congrAdd (congrApp1 r (iter_zero T _)) (.eqRefl _)).eqTrans
      (add_zero _)).eqSymm (.eqRefl _) (le_refl _)
  · simp only [invF, Fm.subst_imp, Fm.subst_and, Fm.subst_or, Fm.subst_eq, subst_le, subst_app1,
      subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [invF T r D V] ⊢[PRAAx] (app1 V (var 1) ≐ one) ⟶
        ((app1 V (iter T (var 0) (var 1)) ≐ one) ⋏
          ((app1 D (iter T (var 0) (var 1)) ≐ one) ⋎
            le (app1 r (iter T (var 0) (var 1)) + var 0) (app1 r (var 1)))) := Prf.hyp0
    refine .impI ?_
    have r' := Prf.impE ih.wk Prf.hyp0
    exact inv_step H (Prf.andE₁ r') (Prf.andE₂ r')

/-- The invariant of `thm:rank` along the iteration. -/
theorem descent_inv (H : Descent T r D V) {s₀ : PTm k} (h₀ : Γ ⊢[PRAAx] app1 V s₀ ≐ one)
    (t : PTm k) :
    Γ ⊢[PRAAx] (app1 V (iter T t s₀) ≐ one) ⋏
      ((app1 D (iter T t s₀) ≐ one) ⋎ le (app1 r (iter T t s₀) + t) (app1 r s₀)) := by
  have i := inst (Γ := Γ) (inv₀ H) (![t, s₀] : Fin 2 → PTm k)
  simp [invF] at i
  exact .impE i h₀

/-- `thm:rank`: the iterate `T^{r(s₀)}(s₀)` of a valid state is terminal. -/
theorem terminal (H : Descent T r D V) {s₀ : PTm k} (h₀ : Γ ⊢[PRAAx] app1 V s₀ ≐ one) :
    Γ ⊢[PRAAx] app1 D (iter T (app1 r s₀) s₀) ≐ one := by
  have i := descent_inv H h₀ (app1 r s₀)
  refine .orE (Prf.andE₂ i) Prf.hyp0 ?_
  refine .orE (eq_or_ne (app1 D (iter T (app1 r s₀) s₀)) one) Prf.hyp0 ?_
  -- a nonterminal state of rank zero would have a successor of negative rank
  have hdec := H.dec ((Prf.andE₁ i).wk
    (ψ := le (app1 r (iter T (app1 r s₀) s₀) + app1 r s₀) (app1 r s₀))).wk
    (Prf.hyp0 (Γ := le (app1 r (iter T (app1 r s₀) s₀) + app1 r s₀) (app1 r s₀) :: Γ)
      (φ := neg (app1 D (iter T (app1 r s₀) s₀) ≐ one)))
  have e₁ := natEq (eq_add_of_le hdec)
  have e₂ := natEq (eq_add_of_le (Prf.hyp1 (Γ := Γ)
    (φ := le (app1 r (iter T (app1 r s₀) s₀) + app1 r s₀) (app1 r s₀))
    (ψ := neg (app1 D (iter T (app1 r s₀) s₀) ≐ one))))
  refine not_succ_le_self (app1 r (app1 T (iter T (app1 r s₀) s₀)) + app1 r s₀) _
    (le_of_eq_add (d := monus (app1 r (iter T (app1 r s₀) s₀))
      (succ (app1 r (app1 T (iter T (app1 r s₀) s₀)))) +
      monus (app1 r s₀) (app1 r (iter T (app1 r s₀) s₀) + app1 r s₀) +
      app1 r (app1 T (iter T (app1 r s₀) s₀))) ?_)
  apply deriveNat; ipra_simps
  linear_combination e₂ + e₁

/-- `thm:rank` as a closed sentence. Variable: `0 = s₀`. -/
theorem terminal_closed (H : Descent T r D V) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((app1 V (var 0) ≐ one) ⟶ (app1 D (iter T (app1 r (var 0)) (var 0)) ≐ one)) :=
  closeUniv 1 (.impI (terminal H Prf.hyp0))

end Rank

/-! ## An instance: counting down -/

/-- `T(s) = s ∸ 1`. -/
def predT : PTm 1 := pred (var 0)
/-- `r(s) = s`. -/
def idT : PTm 1 := var 0
/-- `D(s) = [s = 0]`. -/
def zeroTest : PTm 1 := eqb (var 0) zero
/-- `V(s) = 1`. -/
def trueT : PTm 1 := one

theorem app1_predT (s : PTm k) : app1 predT s = pred s := by simp [app1, predT]
theorem app1_idT (s : PTm k) : app1 idT s = s := by simp [app1, idT]
theorem app1_zeroTest (s : PTm k) : app1 zeroTest s = eqb s zero := by simp [app1, zeroTest]
theorem app1_trueT (s : PTm k) : app1 trueT s = one := by simp [app1, trueT]

/-- Counting down by the predecessor satisfies the hypotheses of `thm:rank`. -/
theorem countdown : Descent predT idT zeroTest trueT where
  pres := fun _ => by rw [app1_trueT]; exact .eqRefl _
  fix := fun _ hd => by
    rw [app1_zeroTest] at hd
    rw [app1_predT]
    have z := eq_of_eqb hd
    exact (congrPred z).eqTrans (pred_zero.eqTrans z.eqSymm)
  dec := fun {k Γ s} _ hd => by
    rw [app1_zeroTest] at hd
    rw [app1_idT, app1_idT, app1_predT]
    refine .orE (zero_or_succ s) (.botE _ (.impE hd.wk (eqb_of_eq Prf.hyp0))) ?_
    exact le_congr (.eqRefl _) (Prf.hyp0 (Γ := Γ) (φ := s ≐ succ (pred s))).eqSymm (le_refl _)

/-- `pred^{s}(s) = 0` for every `s`, as a closed sentence with all hypotheses discharged. -/
theorem countdown_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (iter predT (var 0) (var 0) ≐ zero) := by
  refine closeUniv 1 ?_
  have t := terminal (Γ := ([] : List (Fm PTm 1))) countdown (s₀ := var 0)
    (by rw [app1_trueT]; exact .eqRefl _)
  rw [app1_zeroTest, app1_idT] at t
  exact eq_of_eqb t

end LeanProofs.IPRA.Foundations.BoundedDescent
