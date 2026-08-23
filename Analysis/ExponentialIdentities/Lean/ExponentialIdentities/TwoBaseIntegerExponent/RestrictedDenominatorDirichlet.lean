import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Covolume conservation for restricted-denominator approximation

One proposed route to the two-base problem forces approximation denominators `q` to carry a
prescribed amount of `p`-adic divisibility (`q ∈ L ℤ` with `L = ∏ p^{e_p}`) and then combines
real and `p`-adic smallness.  The lattice `{(q, qβ - a) : q ∈ Lℤ, a ∈ ℤ}` has covolume `L`, so
Minkowski (or, as here, Dirichlet's pigeonhole) guarantees `|qβ - a| ≲ L / Q` for some
`0 < q ≤ Q` with `L ∣ q` — and every such `q` has `∏_{p ∣ L} |q|_p ≤ 1/L`.  The product
`|qβ - a| · ∏_p |q|_p ≲ 1/Q` is therefore exactly the unrestricted Dirichlet scale: forcing
local depth costs precisely the same factor in the guaranteed real scale.  This file records
that budget identity.

* `exists_restricted_denominator_approx`: for every `L ≥ 1`, `n ≥ 1` and real `β` there are
  `a ∈ ℤ` and `0 < k ≤ n` with `|(kL) β - a| ≤ 1/(n+1)`; in terms of the restricted
  denominator `q = kL ≤ nL` this is `|qβ - a| ≤ L/q` (`exists_restricted_denominator_approx'`);
* `padicValInt_le_of_dvd`: any `q` divisible by `L` has `v_p(q) ≥ v_p(L)`, so its normalized
  `p`-adic absolute value is at most `p^{-v_p(L)}`;
* `covolume_conservation`: for `L = p^e`, `|qβ - a| · p^{-v_p(q)} ≤ 1/q` — the unrestricted
  Dirichlet scale.  The several-prime version is the product of the local factors.
-/

namespace LeanProofs.TwoBaseIntegerExponent.RestrictedDirichlet

/-- **Restricted-denominator Dirichlet.**  For every `L` and `n ≥ 1`, some multiple `q = kL`
with `0 < k ≤ n` satisfies `|qβ - a| ≤ 1/(n+1)`. -/
theorem exists_restricted_denominator_approx (β : ℝ) (L : ℕ) {n : ℕ} (hn : 0 < n) :
    ∃ a k : ℤ, 0 < k ∧ k ≤ n ∧ |((k * L : ℤ) : ℝ) * β - a| ≤ 1 / (n + 1) := by
  obtain ⟨a, k, hk0, hkn, h⟩ := Real.exists_int_int_abs_mul_sub_le ((L : ℝ) * β) hn
  refine ⟨a, k, hk0, hkn, ?_⟩
  push_cast
  rw [mul_assoc]
  exact h

/-- The real scale achieved, expressed against the restricted denominator `q = kL ≤ nL`:
`|qβ - a| ≤ 1/(n+1) ≤ L / q`. -/
theorem exists_restricted_denominator_approx' (β : ℝ) {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    ∃ a q : ℤ, 0 < q ∧ (L : ℤ) ∣ q ∧ q ≤ n * L ∧ |(q : ℝ) * β - a| ≤ (L : ℝ) / q := by
  obtain ⟨a, k, hk0, hkn, h⟩ := exists_restricted_denominator_approx β L hn
  refine ⟨a, k * L, by positivity, dvd_mul_left _ _, by nlinarith, ?_⟩
  refine h.trans ?_
  have hq : (0 : ℝ) < ((k * L : ℤ) : ℝ) := by exact_mod_cast (mul_pos hk0 (by exact_mod_cast hL))
  rw [div_le_div_iff₀ (by positivity) hq, one_mul]
  push_cast
  have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith

/-- The forced local factor: if `L ∣ q` then `v_p(q) ≥ v_p(L)` for every prime `p`. -/
theorem padicValInt_le_of_dvd {p : ℕ} [Fact p.Prime] {L q : ℤ} (hq : q ≠ 0) (h : L ∣ q) :
    padicValInt p L ≤ padicValInt p q := by
  obtain ⟨c, rfl⟩ := h
  have hL : L ≠ 0 := left_ne_zero_of_mul hq
  have hc : c ≠ 0 := right_ne_zero_of_mul hq
  rw [padicValInt.mul hL hc]
  exact Nat.le_add_right _ _

/-- **Covolume conservation** (one prime; the general case is the product over `p ∣ L`).
Forcing `p^e ∣ q` and applying Dirichlet to the restricted lattice, the product of the
guaranteed real scale `|qβ - a|` and the forced local factor `p^{-v_p(q)} ≤ p^{-e}` is at most
`1/q`, the unrestricted Dirichlet scale.  Imposing denominator divisibility buys no adelic
exponent. -/
theorem covolume_conservation (β : ℝ) {p : ℕ} [hp : Fact p.Prime] (e : ℕ) {n : ℕ} (hn : 0 < n) :
    ∃ a q : ℤ, 0 < q ∧ ((p : ℤ) ^ e) ∣ q ∧ q ≤ n * p ^ e ∧
      |(q : ℝ) * β - a| * ((p : ℝ) ^ padicValInt p q)⁻¹ ≤ 1 / q := by
  obtain ⟨a, q, hq0, hdvd, hqle, h⟩ :=
    exists_restricted_denominator_approx' β (L := p ^ e) (pow_pos hp.out.pos e) hn
  push_cast at hdvd hqle
  refine ⟨a, q, hq0, hdvd, hqle, ?_⟩
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hval : e ≤ padicValInt p q := by
    have := padicValInt_le_of_dvd (p := p) hq0.ne' hdvd
    rwa [show ((p : ℤ) ^ e) = ((p ^ e : ℕ) : ℤ) by push_cast; rfl, padicValInt.of_nat,
      padicValNat.prime_pow] at this
  have hpow : (p : ℝ) ^ e ≤ (p : ℝ) ^ padicValInt p q := pow_le_pow_right₀ hp1 hval
  have hpe : (0 : ℝ) < (p : ℝ) ^ e := by positivity
  push_cast at h
  calc |(q : ℝ) * β - a| * ((p : ℝ) ^ padicValInt p q)⁻¹
      ≤ ((p : ℝ) ^ e / q) * ((p : ℝ) ^ e)⁻¹ := by
        gcongr
    _ = 1 / q := by field_simp

end LeanProofs.TwoBaseIntegerExponent.RestrictedDirichlet
