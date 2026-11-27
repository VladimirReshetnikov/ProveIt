import IPRADerivations.Foundations.AutomaticLexFuel

/-!
# An instance of automatic fuel: the countdown (`ipra_resources_and_elimination_2026-11-15`, `thm:automatic-lex-fuel`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, theorem `thm:automatic-lex-fuel`.
`Foundations/AutomaticLexFuel` derives the theorem from four premises given as rules. This
module discharges all four for one transition system, so that the theorem is used with no
hypothesis left:

* state `u`, transition `τ(x, u) = u ∸ 1`, active when `u ≠ 0`, one rank `r_0 = u`, trivial
  invariant, arbitrary initial state `u_0(x)`;
* `countdown`: the state at time `B(x) = F_1(x, 0)` is `0`, where the envelope is the maximum
  of the states visited so far;
* `countdown_closed`: the same as a closed sentence for the initial state `u_0(x) = x`.

The four premises here are: the invariant is initialized and preserved (trivially),
`u = 0 ⟹ u ∸ 1 = 0`, and `u ≠ 0 ⟹ u ∸ 1 < u`.
-/

namespace LeanProofs.IPRA.Foundations.AutomaticLexFuelExample

open_ipra exports
open LeanProofs.IPRA.Foundations.IterationFusion (rel)
open LeanProofs.IPRA.Foundations.AutomaticLexFuel (traj fuel automatic_fuel)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `τ(x, u) = u ∸ 1`; variables `0 = x`, `1 = u`. -/
def tauC : PTm 2 := pred (var 1)

/-- The activity bit: active when `u ≠ 0`. -/
def actC : PTm 2 := var 1

/-- The single rank `r_0(x, u) = u`. -/
def rkC : Fin 1 → PTm 2 := fun _ => var 1

/-- The trivial invariant. -/
def invC : Fm PTm 2 := (zero : PTm 2) ≐ zero

theorem tau_at (x u : PTm k) : inst2 tauC x u = pred u := by simp [inst2, tauC]

theorem act_at (x u : PTm k) : inst2 actC x u = u := by simp [inst2, actC]

theorem rk_at (j : Fin 1) (x u : PTm k) : inst2 (rkC j) x u = u := by simp [inst2, rkC]

theorem inv_at' (x u : PTm k) : rel invC x u = ((zero : PTm k) ≐ zero) := by simp [rel, invC]

/-- The countdown reaches `0` within the automatic fuel. -/
theorem countdown (u0 : PTm 1) (x : PTm k) :
    Γ ⊢[PRAAx] traj tauC u0 (fuel tauC u0 rkC x) x ≐ zero := by
  have h := automatic_fuel (Γ := Γ) tauC u0 invC actC rkC
    (show ((zero : PTm 2) ≐ zero).QF from trivial)
    (fun x => by rw [inv_at']; exact .eqRefl _)
    (fun _ => by rw [inv_at']; exact .eqRefl _)
    (fun {k Γ x u} h => by
      rw [act_at] at h ⊢
      rw [tau_at]
      exact (congrPred h).eqTrans pred_zero)
    (fun {k Γ x u} _ ha _ => by
      rw [act_at] at ha
      simp only [rk_at, tau_at]
      refine .orI₁ ?_
      refine .orE (zero_or_succ u) (.botE _ (.impE ha.wk Prf.hyp0)) ?_
      exact le_congr Prf.hyp0 (.eqRefl _) (le_refl u))
    x
  rw [act_at] at h
  exact h

/-- The countdown from `x`, as a closed sentence. -/
theorem countdown_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (traj tauC (var 0) (fuel tauC (var 0) rkC (var 0)) (var 0) ≐ zero) :=
  closeUniv 1 (countdown _ _)

end LeanProofs.IPRA.Foundations.AutomaticLexFuelExample
