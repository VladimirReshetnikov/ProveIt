import IPRADerivations.AnalyticNumberTheory.Primes
import IPRADerivations.Core.OrderCertificates

/-!
# The partial sums of `e`

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Section "A finite proof that `log e = 1`", `eq:etail`:
`j! ≥ 2^{j−1}`, and for `E_m = ∑_{j ≤ m} 1/j!`, `E_m ≤ 3` with the tail `∑_{j>m} 1/j! ≤ 1/(m · m!)`.

`E_m` is cleared by `m!`: `en m = ∑_{j ≤ m} m!/j! = m! E_m`, defined by `en 0 = 1`,
`en (m + 1) = (m + 1) · en m + 1`.

* `two_pow_le_fact`: `2^{j+1} ≤ 2 (j + 1)!`, i.e. `j! ≥ 2^{j−1}` for `j ≥ 1`;
* `en_ge`: `2 (m + 1)! ≤ en (m + 1)`, i.e. `E_m ≥ 2` for `m ≥ 1`;
* `tail_step`: `E_{m+1} + 1/((m+1)(m+1)!) ≤ E_m + 1/(m · m!)` for `m ≥ 1`, cleared: the partial sums with the
  tail bound added decrease, which is the finite content of `∑_{j>m} 1/j! ≤ 1/(m · m!)`;
* `en_upper`: `m · en m + 1 ≤ 3 m · m!` for `m = m₀ + 1`, i.e. `E_m + 1/(m · m!) ≤ 3` (equality at `m = 1`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ExponentialSeries

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem fact_succ' (m : PTm n) : Γ ⊢[PRAAx] fact (succ m) ≐ fact m * succ m := fact_succ m zero
theorem fact_zero' : Γ ⊢[PRAAx] fact (zero : PTm n) ≐ succ zero := fact_zero zero

/-! ## `j! ≥ 2^{j−1}` -/

theorem tp_base : Γ ⊢[PRAAx] le (pw two (succ (zero : PTm n))) (two * fact (succ zero)) := by
  have f1 := natEq (fact_succ' (Γ := Γ) zero); have f0 := natEq (fact_zero' (Γ := Γ))
  have p1 := natEq (pw_succ (Γ := Γ) two zero); have p0 := natEq (pw_zero (Γ := Γ) (two : PTm n))
  ipra_le 0 using rw [f1, f0, p1, p0]; ring

theorem tp_step {j : PTm n} (ih : Γ ⊢[PRAAx] le (pw two (succ j)) (two * fact (succ j))) :
    Γ ⊢[PRAAx] le (pw two (succ (succ j))) (two * fact (succ (succ j))) := by
  have f := natEq (fact_succ' (Γ := Γ) (succ j)); have p := natEq (pw_succ (Γ := Γ) two (succ j))
  ipra_le 2 * sl ih + 2 * 𝔞 j * 𝔞 (fact (succ j)) using rw [f, p]; ring

/-- Variable `0 = j`. -/
private abbrev tpF : Fm PTm 1 := le (pw two (succ (var 0))) (two * fact (succ (var 0)))

private theorem tp₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] tpF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact tp_base
  · exact tp_step Prf.hyp0

/-- `eq:etail`, first part: `2^{j+1} ≤ 2 (j + 1)!`. -/
theorem two_pow_le_fact (j : PTm n) : Γ ⊢[PRAAx] le (pw two (succ j)) (two * fact (succ j)) := by
  have h := inst (Γ := Γ) tp₀ (![j] : Fin 1 → PTm n)
  simp at h
  exact h

/-! ## The cleared partial sums -/

/-- Step of `en`: variables `0 = m`, `1 = en m`, `2` unused. -/
abbrev enStep : PTm 3 := succ (var 0) * var 1 + succ zero
abbrev enF : PR 2 := rec2 (succ zero) enStep

/-- `en m = ∑_{j ≤ m} m!/j! = m! E_m`. -/
abbrev en (m : PTm n) : PTm n := ap2 enF m zero

theorem en_zero : Γ ⊢[PRAAx] en (zero : PTm n) ≐ succ zero := by
  have h := rec2_zero (Γ := Γ) (succ zero) enStep (zero : PTm n)
  simpa using h

theorem en_succ (m : PTm n) : Γ ⊢[PRAAx] en (succ m) ≐ succ m * en m + succ zero := by
  have h := rec2_succ (Γ := Γ) (succ zero) enStep m (zero : PTm n)
  simpa using h

/-! ## `2 ≤ E_m` -/

theorem ge_base : Γ ⊢[PRAAx] le (two * fact (succ (zero : PTm n))) (en (succ zero)) := by
  have f1 := natEq (fact_succ' (Γ := Γ) zero); have f0 := natEq (fact_zero' (Γ := Γ))
  have e1 := natEq (en_succ (Γ := Γ) zero); have e0 := natEq (en_zero (Γ := Γ))
  ipra_le 0 using rw [f1, f0, e1, e0]; ring

theorem ge_step {m : PTm n} (ih : Γ ⊢[PRAAx] le (two * fact (succ m)) (en (succ m))) :
    Γ ⊢[PRAAx] le (two * fact (succ (succ m))) (en (succ (succ m))) := by
  have f := natEq (fact_succ' (Γ := Γ) (succ m)); have e := natEq (en_succ (Γ := Γ) (succ m))
  ipra_le (𝔞 m + 2) * sl ih + 1 using rw [f, e]; ring

private abbrev geF : Fm PTm 1 := le (two * fact (succ (var 0))) (en (succ (var 0)))

private theorem ge₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] geF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact ge_base
  · exact ge_step Prf.hyp0

/-- `E_m ≥ 2` for `m ≥ 1`: `2 (m + 1)! ≤ en (m + 1)`. -/
theorem en_ge (m : PTm n) : Γ ⊢[PRAAx] le (two * fact (succ m)) (en (succ m)) := by
  have h := inst (Γ := Γ) ge₀ (![m] : Fin 1 → PTm n)
  simp at h
  exact h

/-! ## The tail bound and `E_m ≤ 3` -/

/-- `E_{m+1} + 1/((m+1)(m+1)!) ≤ E_m + 1/(m · m!)` for `m = m₀ + 1`, cleared by `m (m+1) (m+1)!`:
`m (m+1) · en (m+1) + m ≤ m (m+1)² · en m + (m+1)²`. -/
theorem tail_step (m₀ : PTm n) :
    Γ ⊢[PRAAx] le (succ m₀ * succ (succ m₀) * en (succ (succ m₀)) + succ m₀)
      (succ m₀ * (succ (succ m₀) * succ (succ m₀)) * en (succ m₀) + succ (succ m₀) * succ (succ m₀)) := by
  have e := natEq (en_succ (Γ := Γ) (succ m₀))
  ipra_le 1 using rw [e]; ring

/-- `m · en m + 1 ≤ 3 m · m!` for `m = m₀ + 1`. -/
abbrev UpInv (m₀ : PTm n) : Fm PTm n :=
  le (succ m₀ * en (succ m₀) + succ zero) (num 3 * (succ m₀ * fact (succ m₀)))

theorem up_base : Γ ⊢[PRAAx] UpInv (zero : PTm n) := by
  have f1 := natEq (fact_succ' (Γ := Γ) zero); have f0 := natEq (fact_zero' (Γ := Γ))
  have e1 := natEq (en_succ (Γ := Γ) zero); have e0 := natEq (en_zero (Γ := Γ))
  ipra_le 0 using rw [f1, f0, e1, e0]; ring

theorem up_step {m₀ : PTm n} (ih : Γ ⊢[PRAAx] UpInv m₀) : Γ ⊢[PRAAx] UpInv (succ m₀) := by
  have f := natEq (fact_succ' (Γ := Γ) (succ m₀)); have e := natEq (en_succ (Γ := Γ) (succ m₀))
  refine mul_le_cancel (d' := m₀) ?_
  ipra_le (𝔞 m₀ + 2) * (𝔞 m₀ + 2) * sl ih + 1 using rw [f, e]; ring

private abbrev upF : Fm PTm 1 := UpInv (var 0)

private theorem up₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] upF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact up_base
  · exact up_step Prf.hyp0

/-- `eq:etail`: `E_m + 1/(m · m!) ≤ 3` for `m = m₀ + 1 ≥ 1`, cleared: `m · en m + 1 ≤ 3 m · m!`. -/
theorem en_upper (m₀ : PTm n) : Γ ⊢[PRAAx] UpInv m₀ := by
  have h := inst (Γ := Γ) up₀ (![m₀] : Fin 1 → PTm n)
  simp at h
  exact h

end LeanProofs.IPRA.Analysis.ExponentialSeries
