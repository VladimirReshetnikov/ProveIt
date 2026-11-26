import IPRADerivations.Core.Powers
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.LinearCombination

/-!
# Rational closure: eliminating a vanishing dyadic error

Packets: `analysis/calculus_ipra` (the lemma "Rational closure" of Section "Eliminating limiting
shorthand") and `analysis/taylor_cauchy_ipra` (`lem:closure`). If rationals `u, v, C` with
`C ≥ 0` satisfy `u ≤ v + C 2⁻ⁿ` for every `n`, then `u ≤ v`. After multiplication by `2ⁿ` and by
a common denominator this is a statement about natural numbers:

* `succ_le_two_pow`: `m + 1 ≤ 2^m`;
* `closure`: if `2ⁿ u ≤ 2ⁿ v + C` for every `n`, then `u ≤ v`.

The proof decides `v < u` and, in that case, instantiates the hypothesis at `n = C`; no unbounded
search is used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalClosure

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem pow_step {m : PTm n} (ih : Γ ⊢[PRAAx] le (succ m) (pw two m)) :
    Γ ⊢[PRAAx] le (succ (succ m)) (pw two (succ m)) := by
  refine le_trans (le_of_eq_add (d := m) ?_)
    (le_congr (.eqRefl _) (pw_succ _ _).eqSymm (le_mul_mono ih (le_refl two)))
  ipra_ring

/-- Variables: `0 = m`. -/
private abbrev powF' : Fm PTm 1 := le (succ (var 0)) (pw two (var 0))

private theorem pow₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] powF' := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact le_congr (.eqRefl _) (pw_zero _).eqSymm (le_refl one)
  · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact pow_step Prf.hyp0

/-- `m + 1 ≤ 2^m`. -/
theorem succ_le_two_pow (m : PTm n) : Γ ⊢[PRAAx] le (succ m) (pw two m) := by
  have h := inst (Γ := Γ) pow₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-- `v < u` contradicts `2^C u ≤ 2^C v + C`. -/
theorem closure_aux {u v C : PTm n} (φ : Fm PTm n) (hlt : Γ ⊢[PRAAx] lt v u)
    (hi : Γ ⊢[PRAAx] le (pw two C * u) (pw two C * v + C)) : Γ ⊢[PRAAx] φ := by
  have e₁ : Γ ⊢[PRAAx] pw two C * u ≐
      (pw two C + pw two C * monus u (succ v)) + pw two C * v := by
    ipra_lc 𝔞(pw two C) * natEq (eq_add_of_le hlt)
  have hP : Γ ⊢[PRAAx] le (pw two C + pw two C * monus u (succ v)) C :=
    le_of_add_le_add_right (le_congr e₁ (add_comm _ _) hi)
  exact not_succ_le_self C φ (le_trans (succ_le_two_pow C) (le_trans (le_add_right _ _) hP))

/-- Rational closure: if `2ⁿ u ≤ 2ⁿ v + C` for every `n`, then `u ≤ v`. -/
theorem closure {u v C : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (le (pw two (var 0) * Syn.shift u) (pw two (var 0) * Syn.shift v + Syn.shift C))) :
    Γ ⊢[PRAAx] le u v := by
  have hi : Γ ⊢[PRAAx] le (pw two C * u) (pw two C * v + C) := by
    simpa using Prf.allE C h
  exact .orE (lt_or_le v u) (closure_aux _ Prf.hyp0 hi.wk) Prf.hyp0

end LeanProofs.IPRA.Analysis.RationalClosure
