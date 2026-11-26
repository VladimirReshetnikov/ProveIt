import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Powers

/-!
# The elimination steps of the Stirling estimate

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Sections `sec:factorial`, `sec:exp` and
`sec:elimination`. Once the analytic inputs are available as rational inequalities at a fixed precision,
the passage from the telescoped Robbins inequality to the final bounds is linear arithmetic. All
quantities are numerators over one common denominator and are parameters here.

* `terminal_upper`, `terminal_lower` (`eq:terminal`): from `F_m = 2 a_m − a_{2m}` (as `F + a' = a + a`),
  `C ≤ F_m ≤ C + 1/(4m)` (`eq:Fbound`) and `0 ≤ a_m − a_{2m} ≤ 1/(24m)` (`eq:weaktel`):
  `−1/(24m) ≤ a_m − C ≤ 1/(4m)`.
* `finite_final_lower`, `finite_final_upper` (`eq:finitefinal`): from `eq:strongtel` at `(n, m)`, the
  terminal estimate, `g_m ≤ 1/(12m) = h_m`, `1/(24m) + 1/(12m) ≤ 1/(8m)` and `1/(4m) ≤ 1/(12m) + 1/(6m)`:
  `g_n + λ_n − 1/(8m) ≤ a_n − C ≤ h_n − μ_n + 1/(6m)`.
* `q_finite_lower`, `q_finite_upper` (`eq:Qfinite`): with `|Q(n, p) − (a_n − C)| ≤ d` (`eq:Qerr`):
  `g_n + λ_n − 1/(8m) − d ≤ Q ≤ h_n − μ_n + 1/(6m) + d`.
* `three_pow_le_four_pow`, `lin_le_four_pow` (the last step of `eq:Herr`): `3^n ≤ 4^n` and
  `3n + 1 ≤ 4^n` for `n ≥ 1`.

The removal of the auxiliary errors `1/(8m)`, `1/(6m)` is `lem:gap` (`Analysis/GapRemoval`). The inputs
`eq:Fbound`, `eq:Qerr`, which use the logarithm names, are hypotheses.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.StirlingElimination

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The terminal estimate -/

/-- `eq:terminal`, upper half: `a_m − C ≤ 1/(4m)`. -/
theorem terminal_upper {a a' F C e4 : PTm n} (hF : Γ ⊢[PRAAx] F + a' ≐ a + a)
    (hC : Γ ⊢[PRAAx] le F (C + e4)) (hw : Γ ⊢[PRAAx] le a' a) : Γ ⊢[PRAAx] le a (C + e4) := by
  have e := natEq hF
  ipra_le sl hC + sl hw using linear_combination e

/-- `eq:terminal`, lower half: `−1/(24m) ≤ a_m − C`. -/
theorem terminal_lower {a a' F C e24 : PTm n} (hF : Γ ⊢[PRAAx] F + a' ≐ a + a)
    (hC : Γ ⊢[PRAAx] le C F) (hw : Γ ⊢[PRAAx] le a (a' + e24)) : Γ ⊢[PRAAx] le C (a + e24) := by
  have e := natEq hF
  ipra_le sl hC + sl hw using linear_combination -e

/-! ## The finite final estimate -/

/-- `eq:finitefinal`, lower half: `g_n + λ_n − 1/(8m) ≤ a_n − C`. -/
theorem finite_final_lower {an am gn gm lam C e8 e12 e24 : PTm n}
    (h : Γ ⊢[PRAAx] le (gn + lam + am) (an + gm)) (hC : Γ ⊢[PRAAx] le C (am + e24))
    (hg : Γ ⊢[PRAAx] le gm e12) (he : Γ ⊢[PRAAx] le (e24 + e12) e8) :
    Γ ⊢[PRAAx] le (gn + lam + C) (an + e8) := by
  ipra_le sl h + sl hC + sl hg + sl he

/-- `eq:finitefinal`, upper half: `a_n − C ≤ h_n − μ_n + 1/(6m)`. -/
theorem finite_final_upper {an am hn hm mu C e4 e6 e12 : PTm n}
    (h : Γ ⊢[PRAAx] le (an + hm + mu) (hn + am)) (hC : Γ ⊢[PRAAx] le am (C + e4))
    (he : Γ ⊢[PRAAx] le e4 (e12 + e6)) (hh : Γ ⊢[PRAAx] le e12 hm) :
    Γ ⊢[PRAAx] le (an + mu) (hn + C + e6) := by
  ipra_le sl h + sl hC + sl he + sl hh

/-- `eq:Qfinite`, lower half: `g_n + λ_n − 1/(8m) − d ≤ Q`. -/
theorem q_finite_lower {an gn lam C e8 Q d : PTm n} (h : Γ ⊢[PRAAx] le (gn + lam + C) (an + e8))
    (hQ : Γ ⊢[PRAAx] le an (Q + C + d)) : Γ ⊢[PRAAx] le (gn + lam) (Q + e8 + d) := by
  ipra_le sl h + sl hQ

/-- `eq:Qfinite`, upper half: `Q ≤ h_n − μ_n + 1/(6m) + d`. -/
theorem q_finite_upper {an hn mu C e6 Q d : PTm n} (h : Γ ⊢[PRAAx] le (an + mu) (hn + C + e6))
    (hQ : Γ ⊢[PRAAx] le (Q + C) (an + d)) : Γ ⊢[PRAAx] le (Q + mu) (hn + e6 + d) := by
  ipra_le sl h + sl hQ

/-! ## The scale of `eq:Herr` -/

/-- `3^n ≤ 4^n`. -/
theorem three_pow_le_four_pow (k : PTm n) : Γ ⊢[PRAAx] le (pw (num 3) k) (pw (num 4) k) :=
  pw_le_pw k (by ipra_le 1)

theorem lin_base : Γ ⊢[PRAAx] le (num 3 * succ (zero : PTm n) + one) (pw (num 4) (succ zero)) := by
  have p1 := natEq (pw_succ (Γ := Γ) (num 4) zero); have p0 := natEq (pw_zero (Γ := Γ) (num 4 : PTm n))
  ipra_le 0 using rw [p1, p0]; ring

theorem lin_step {k : PTm n} (ih : Γ ⊢[PRAAx] le (num 3 * succ k + one) (pw (num 4) (succ k))) :
    Γ ⊢[PRAAx] le (num 3 * succ (succ k) + one) (pw (num 4) (succ (succ k))) := by
  have p := natEq (pw_succ (Γ := Γ) (num 4) (succ k))
  ipra_le 4 * sl ih + 9 * 𝔟 k + 9 using rw [p]; ring

/-- Variable `0 = k`. -/
private abbrev linF : Fm PTm 1 := le (num 3 * succ (var 0) + one) (pw (num 4) (succ (var 0)))

private theorem lin₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] linF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_num, Syn.subst_var, Syn.inst_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact lin_base
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_num, Syn.subst_var, Syn.repl_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact lin_step Prf.hyp0

/-- `3n + 1 ≤ 4^n` for `n = k + 1`. -/
theorem lin_le_four_pow (k : PTm n) : Γ ⊢[PRAAx] le (num 3 * succ k + one) (pw (num 4) (succ k)) := by
  have h := inst (Γ := Γ) lin₀ (![k] : Fin 1 → PTm n)
  simp at h
  exact h

end LeanProofs.IPRA.Analysis.StirlingElimination
