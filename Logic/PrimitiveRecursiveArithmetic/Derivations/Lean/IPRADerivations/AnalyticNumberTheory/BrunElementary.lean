import IPRADerivations.Core.Powers
import IPRADerivations.Core.Parity
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Header

/-!
# Elementary inequalities of the Brun convergence argument

Packet: `analytic-number-theory/brun_ipra_2026-11-15`, `sections/05_convergence.tex`:

* Lemma `lem:polynomial`: "For every `t ≥ 0`, `(t + 1)² ≤ 2^{2t}`", by "induction on a quantifier-free
  numerical inequality" (`sq_le_pow`);
* `eq:telescope-step`: `1/(j + 1)² ≤ 1/(j (j + 1)) = 1/j − 1/(j + 1)`, cleared of denominators
  (`telescope_step`: `j (j + 1) ≤ (j + 1)²` and `(j + 1) = j + 1` for the difference of the two unit
  fractions, i.e. `(j + 1) − j = 1` over the common denominator `j (j + 1)`).

The sieve weights, the dyadic counting theorem and the reciprocal tail are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BrunElementary

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem sq_base : Γ ⊢[PRAAx] le (succ (zero : PTm n) * succ zero) (pw two (two * zero)) := by
  have c := natEq (congrAp2 powF (mul_zero (Γ := Γ) (two : PTm n)) (.eqRefl (two : PTm n)))
  have pz := natEq (pw_zero (Γ := Γ) (two : PTm n))
  ipra_le 0 using linear_combination c + pz

theorem sq_step {t : PTm n} (ih : Γ ⊢[PRAAx] le (succ t * succ t) (pw two (two * t))) :
    Γ ⊢[PRAAx] le (succ (succ t) * succ (succ t)) (pw two (two * succ t)) := by
  have e₂ : Γ ⊢[PRAAx] two * succ t ≐ succ (succ (two * t)) := by
    ipra_ring
  have c := natEq (congrAp2 powF e₂ (.eqRefl (two : PTm n)))
  have p₁ := natEq (pw_succ (Γ := Γ) two (succ (two * t)))
  have p₂ := natEq (pw_succ (Γ := Γ) two (two * t))
  ipra_le 4 * sl ih + 3 * 𝔟 t * 𝔟 t + 4 * 𝔟 t using linear_combination c + p₁ + 2 * p₂

/-- Variables: `0 = t`. -/
private abbrev sqF : Fm PTm 1 := le (succ (var 0) * succ (var 0)) (pw two (two * var 0))

private theorem sq₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] sqF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · have e : sqF.subst (Syn.inst zero) =
        (le (succ zero * succ zero) (pw two (two * zero)) : Fm PTm 0) := by
      simp
    rw [e]
    exact sq_base
  · have e : sqF.subst (repl (succ (var 0))) =
        (le (succ (succ (var 0)) * succ (succ (var 0))) (pw two (two * succ (var 0))) : Fm PTm 1) := by
      simp
    rw [e]
    exact sq_step Prf.hyp0

/-- `lem:polynomial`: `(t + 1)² ≤ 2^{2t}`. -/
theorem sq_le_pow (t : PTm n) : Γ ⊢[PRAAx] le (succ t * succ t) (pw two (two * t)) := by
  have h := inst (Γ := Γ) sq₀ (![t] : Fin 1 → PTm n)
  simpa using h

/-- `eq:telescope-step`, cleared: `j (j + 1) ≤ (j + 1)²`, so `1/(j + 1)² ≤ 1/(j (j + 1))`. -/
theorem telescope_step (j : PTm n) : Γ ⊢[PRAAx] le (j * succ j) (succ j * succ j) := by
  ipra_le 𝔟 j + 1

end LeanProofs.IPRA.AnalyticNumberTheory.BrunElementary
