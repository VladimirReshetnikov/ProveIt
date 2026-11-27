import IPRADerivations.Core.PolynomialImplications
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Parity
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# Dyadic band sums and the 3–4–1 polynomial

Packet: `analytic-number-theory/zeta_zeros_ipra_2026-11-15`.

* `sections/consequences.tex`, Theorem "Uniform reciprocal-square tail" (`eq:reciprocal-tail`). After the
  band count, the proof sums `∑_{j<J} 2^{-j} (a + (j + 1) b)` over finitely many dyadic bands, "a finite
  geometric sum and its explicit remainder", uniformly in the number `J` of bands. With the numerators
  over the denominator `2^J`,

  `G_J = 2^J ∑_{j<J} 2^{-j}` (`G_0 = 0`, `G_{J+1} = 2 G_J + 2`),
  `R_J = 2^J ∑_{j<J} (j + 1) 2^{-j}` (`R_0 = 0`, `R_{J+1} = 2 R_J + 2 (J + 1)`),

  the explicit remainders are `geometric`: `G_J + 2 = 2 · 2^J`, and `weighted`: `R_J + 2 (J + 2) = 4 · 2^J`;
  hence `band_sum`: `a G_J + b R_J ≤ 2^J (2a + 4b)`, i.e. the band sum is at most `2a + 4b` for every
  `J`. No convergence statement is quantified over.
* `sections/elementary.tex`, Lemma `lem:elem-341` ("Euler positivity"): the polynomial identity
  `3 + 4c + (2c² − 1) = 2 (1 + c)²` behind `3 + 4 cos u + cos 2u = 2 (1 + cos u)² ≥ 0`, as a closed
  sentence over the integers (`three_four_one`).

The zero count `eq:coarse-count`, the logarithm bounds and the analytic statements of the packet are not
derived.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DyadicBandSum

open_ipra exports

/-! ## The 3–4–1 polynomial -/

section Identity

open ZExp

local notation "c" => (ZExp.var 0 : ZExp 1)

/-- `3 + 4c + (2c² − 1) = 2 (1 + c)²`. -/
theorem three_four_one :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 1)
      (imp [] ((1 + 1 + 1) + (c + c + c + c) + ((c ^ 2 + c ^ 2) - 1), (1 + c) ^ 2 + (1 + c) ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Identity

/-! ## The band numerators -/

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Step of `G`: variables `0 = J`, `1 = G_J`, `2 = ` unused parameter. -/
abbrev gStep : PTm 3 := var 1 + var 1 + succ (succ zero)

/-- Step of `R`: `R_{J+1} = 2 R_J + 2 (J + 1)`. -/
abbrev rStep : PTm 3 := var 1 + var 1 + (succ (var 0) + succ (var 0))

/-- `G_J = 2^J ∑_{j<J} 2^{-j}`. -/
abbrev Gs (J : PTm n) : PTm n := ap2 (rec2 zero gStep) J zero

/-- `R_J = 2^J ∑_{j<J} (j + 1) 2^{-j}`. -/
abbrev Rs (J : PTm n) : PTm n := ap2 (rec2 zero rStep) J zero

theorem G_zero : Γ ⊢[PRAAx] Gs (zero : PTm n) ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero gStep zero

theorem G_succ (J : PTm n) : Γ ⊢[PRAAx] Gs (succ J) ≐ Gs J + Gs J + succ (succ zero) := by
  have h := rec2_succ (Γ := Γ) zero gStep J zero
  simp only [PTm.subst_add, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  exact h

theorem R_zero : Γ ⊢[PRAAx] Rs (zero : PTm n) ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero rStep zero

theorem R_succ (J : PTm n) : Γ ⊢[PRAAx] Rs (succ J) ≐ Rs J + Rs J + (succ J + succ J) := by
  have h := rec2_succ (Γ := Γ) zero rStep J zero
  simp only [PTm.subst_add, ConciseIPRA.PTm.subst_succ, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

/-! ## The explicit remainders -/

theorem g_base : Γ ⊢[PRAAx] Gs (zero : PTm n) + two ≐ two * pw two zero := by
  have z := natEq (G_zero (Γ := Γ)); have p := natEq (pw_zero (Γ := Γ) two)
  apply deriveNat; ipra_simps
  rw [z, p]; ring

theorem g_step {J : PTm n} (ih : Γ ⊢[PRAAx] Gs J + two ≐ two * pw two J) :
    Γ ⊢[PRAAx] Gs (succ J) + two ≐ two * pw two (succ J) := by
  have es := natEq (G_succ (Γ := Γ) J); have ep := natEq (pw_succ (Γ := Γ) two J)
  have i := natEq ih
  apply deriveNat; ipra_simps
  rw [es, ep]; linear_combination 2 * i

theorem r_base :
    Γ ⊢[PRAAx] Rs (zero : PTm n) + (succ (succ zero) + succ (succ zero)) ≐ (two + two) * pw two zero := by
  have z := natEq (R_zero (Γ := Γ)); have p := natEq (pw_zero (Γ := Γ) two)
  apply deriveNat; ipra_simps
  rw [z, p]; ring

theorem r_step {J : PTm n} (ih : Γ ⊢[PRAAx] Rs J + (succ (succ J) + succ (succ J)) ≐ (two + two) * pw two J) :
    Γ ⊢[PRAAx] Rs (succ J) + (succ (succ (succ J)) + succ (succ (succ J))) ≐ (two + two) * pw two (succ J) := by
  have es := natEq (R_succ (Γ := Γ) J); have ep := natEq (pw_succ (Γ := Γ) two J)
  have i := natEq ih
  apply deriveNat; ipra_simps
  rw [es, ep]; linear_combination 2 * i

private theorem geometric₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] (Gs (var 0) + two ≐ two * pw two (var 0)) := by
  ipra_ind [subst_ap2]
  · exact g_base
  · exact g_step Prf.hyp0

/-- `G_J + 2 = 2 · 2^J`: `∑_{j<J} 2^{-j} = 2 − 2^{1−J}`. -/
theorem geometric (J : PTm n) : Γ ⊢[PRAAx] Gs J + two ≐ two * pw two J := by
  have h := inst (Γ := Γ) geometric₀ (![J] : Fin 1 → PTm n)
  simpa using h

private theorem weighted₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx]
    (Rs (var 0) + (succ (succ (var 0)) + succ (succ (var 0))) ≐ (two + two) * pw two (var 0)) := by
  ipra_ind [subst_ap2]
  · exact r_base
  · exact r_step Prf.hyp0

/-- `R_J + 2 (J + 2) = 4 · 2^J`: `∑_{j<J} (j + 1) 2^{-j} = 4 − (J + 2) 2^{1−J}`. -/
theorem weighted (J : PTm n) :
    Γ ⊢[PRAAx] Rs J + (succ (succ J) + succ (succ J)) ≐ (two + two) * pw two J := by
  have h := inst (Γ := Γ) weighted₀ (![J] : Fin 1 → PTm n)
  simpa using h

/-- The band sum is at most `2a + 4b`, for every number of bands:
`a G_J + b R_J ≤ 2^J (2a + 4b)`. -/
theorem band_sum (a b J : PTm n) :
    Γ ⊢[PRAAx] le (a * Gs J + b * Rs J) (pw two J * (a + a + (b + b + b + b))) := by
  have eG := natEq (geometric (Γ := Γ) J); have eR := natEq (weighted (Γ := Γ) J)
  ipra_le 𝔟 a + 𝔟 a + 𝔟 b * (𝔟 J + 𝔟 J + 4) using linear_combination (-𝔟 a) * eG - 𝔟 b * eR

end LeanProofs.IPRA.AnalyticNumberTheory.DyadicBandSum
