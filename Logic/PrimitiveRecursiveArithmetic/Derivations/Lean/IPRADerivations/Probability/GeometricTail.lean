import IPRADerivations.Probability.GeometricMean
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# The tail modulus of the geometric mean

Packet: `probability/expected_value_ipra_2026-11-16`, Proposition `prop:geometric`, the tail: "Since `q < 1`, a
rational separation `q ≤ 1 − 1/d` is computable from the rational code for `p > 0`. The finite binomial
inequality `(1 − 1/d)^d ≤ 1/2` gives `q^{dm} ≤ 2^{−m}`."

* `bern_hom`: the homogeneous Bernoulli inequality `a^{m+1} + (m+1) a^m b ≤ (a + b)^{m+1}`, by quantifier-free
  induction on `m`;
* `half_bound`: `(1 − 1/d)^d ≤ 1/2`, cleared: `2 e^{e+1} ≤ (e + 1)^{e+1}` for `d = e + 1`;
* `power_half`: `q^{dm} ≤ 2^{−m}` for `q = e/(e + 1)`, cleared: `2^m (e^d)^m ≤ (d^d)^m`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.GeometricTail

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem bern_base (a b : PTm n) :
    Γ ⊢[PRAAx] le (pw a (succ zero) + succ zero * pw a zero * b) (pw (a + b) (succ zero)) := by
  have p1 := natEq (pw_succ (Γ := Γ) a zero)
  have p0 := natEq (pw_zero (Γ := Γ) a)
  have q1 := natEq (pw_succ (Γ := Γ) (a + b) zero)
  have q0 := natEq (pw_zero (Γ := Γ) (a + b))
  refine le_of_eq_add (d := zero) ?_
  apply deriveNat; ipra_simps
  rw [p1, p0, q1, q0]; ring

theorem bern_step {a b m : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw a (succ m) + succ m * pw a m * b) (pw (a + b) (succ m))) :
    Γ ⊢[PRAAx] le (pw a (succ (succ m)) + succ (succ m) * pw a (succ m) * b) (pw (a + b) (succ (succ m))) := by
  have p1 := natEq (pw_succ (Γ := Γ) a m)
  have p2 := natEq (pw_succ (Γ := Γ) a (succ m))
  have p3 := natEq (pw_succ (Γ := Γ) (a + b) (succ m))
  ipra_le (𝔟 a + 𝔟 b) * sl ih + (𝔟 m + 1) * 𝔟 (pw a m) * 𝔟 b ^ 2 using
    rw [p3, p2, p1]; ring

/-- Variables: `0 = m` (induction), `1 = a`, `2 = b`. -/
private abbrev bF : Fm PTm 3 :=
  le (pw (var 1) (succ (var 0)) + succ (var 0) * pw (var 1) (var 0) * var 2) (pw (var 1 + var 2) (succ (var 0)))

private theorem b₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] bF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp
    exact bern_base _ _
  · simp
    exact bern_step Prf.hyp0

/-- The homogeneous Bernoulli inequality `a^{m+1} + (m+1) a^m b ≤ (a + b)^{m+1}`. -/
theorem bern_hom (a b m : PTm n) :
    Γ ⊢[PRAAx] le (pw a (succ m) + succ m * pw a m * b) (pw (a + b) (succ m)) := by
  have h := inst (Γ := Γ) b₀ (![m, a, b] : Fin 3 → PTm n)
  simpa using h

/-- `(1 − 1/d)^d ≤ 1/2`, cleared: `2 e^{e+1} ≤ (e + 1)^{e+1}`. -/
theorem half_bound (e : PTm n) : Γ ⊢[PRAAx] le (num 2 * pw e (succ e)) (pw (succ e) (succ e)) := by
  have h := bern_hom (Γ := Γ) e one e
  have p := natEq (pw_succ (Γ := Γ) e e)
  have c := natEq (congrAp2 (Γ := Γ) powF (.eqRefl (succ e)) (show Γ ⊢[PRAAx] e + one ≐ succ e by
    ipra_ring))
  ipra_le sl h + 𝔟 (pw e e) using
    rw [p] at *
    rw [← c]; ring

/-- `q^{dm} ≤ 2^{−m}` for `q = e/(e + 1)`, `d = e + 1`: `2^m (e^d)^m ≤ (d^d)^m`. -/
theorem power_half (e m : PTm n) :
    Γ ⊢[PRAAx] le (pw (num 2) m * pw (pw e (succ e)) m) (pw (pw (succ e) (succ e)) m) := by
  refine le_congr (mul_pw _ _ m) (.eqRefl _) (pw_le_pw m (half_bound e))

end LeanProofs.IPRA.Probability.GeometricTail
