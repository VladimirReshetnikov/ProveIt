import DiophantineConsistency.Compact44.P72Aux
import DiophantineConsistency.ArithmeticGcdNormalization
import DiophantineConsistency.Compact44.CompactFixedBeta

/-! # P13, section 6: arithmetic for the index congruence

* `β ≡ 1 (mod 3)` for the compact44 numeral `β = 2^590069 − 1`. Since
  `J = 3j+1`, this gives `q = 1 + βJ ≡ 2 (mod 3)`.
* If `q ≡ 2 (mod 3)` and `q³ ∣ Y`, then `H = 4(XY+Y) + 3` is coprime to `q`.
* The gcd cancellation. Let `g0 = gcd(S, H)` and `μ = S/g0`. From
  `(H·x) % S = (H·y) % S` it follows that `x % μ = y % μ`. When `g0 ∣ 3`,
  also `S ≤ 3μ`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P72Mu
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem two_pow_odd_mod (n : ℕ) : (2 ^ (2 * n + 1) - 1) % 3 = 1 := by
  have h : 2 ^ (2 * n + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  have hpos : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
  omega

/-- `2^590069 − 1 ≡ 1 (mod 3)`, by `4^n ≡ 1`. -/
theorem betaNat_mod_three : CompactFixedBeta.betaNat % 3 = 1 := by
  unfold CompactFixedBeta.betaNat
  rw [show (67 * 8807 : ℕ) = 2 * 295034 + 1 from rfl]
  exact two_pow_odd_mod 295034
theorem beta_cast_mod (β : V) (hβ : β = (CompactFixedBeta.betaNat : V)) : ∃ b : V, β = 3 * b + 1 := by
  refine ⟨((CompactFixedBeta.betaNat / 3 : ℕ) : V), ?_⟩
  have h := Nat.div_add_mod CompactFixedBeta.betaNat 3
  rw [betaNat_mod_three] at h
  rw [hβ]
  have := congrArg (fun n : ℕ => (n : V)) h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at this
  exact this.symm

theorem q_mod_three (β j b : V) (hβ : β = 3 * b + 1) :
    ∃ t : V, 1 + β * (3 * j + 1) = 3 * t + 2 :=
  ⟨3 * b * j + b + j, by rw [hβ]; ring⟩

theorem bez_swap {a b g : V} (h : Bez a b g) : Bez b a g := by
  obtain ⟨u, v, w, z, he⟩ := h
  refine ⟨v, u, z, w, ?_⟩
  calc g + b * v + a * u = g + a * u + b * v := by ring
    _ = a * w + b * z := he
    _ = b * z + a * w := by ring

/-- `q ≡ 2 (mod 3)` and `H ≡ 3 (mod q)` make `q` and `H` coprime. -/
theorem bez_q_H (q t w : V) (hq : q = 3 * t + 2) : Bez q (q * w + 3) 1 := by
  refine ⟨1 + w * (t + 1), 0, 0, t + 1, ?_⟩
  rw [hq]; ring

theorem dvd_absdiff_of_mod_eq {a b m : V} (h : a % m = b % m) : m ∣ absdiff a b := by
  have ha := div_add_mod a m
  have hb := div_add_mod b m
  set A := a / m
  set B := b / m
  set r := a % m with hr
  have ha' : a = m * A + r := ha.symm
  have hb' : b = m * B + r := by rw [h]; exact hb.symm
  refine ⟨absdiff A B, ?_⟩
  rw [ha', hb']
  simp only [absdiff, add_tsub_add_eq_tsub_right, mul_tsub, mul_add]

theorem absdiff_mul (h x y : V) : absdiff (h * x) (h * y) = h * absdiff x y := by
  simp only [absdiff, mul_add, mul_tsub]

/-- Cancel `H` modulo `S` up to the gcd. -/
theorem gcd_cancel (S H x y : V) (hS : 0 < S)
    (h : (H * x) % S = (H * y) % S) :
    ∃ g0 μ : V, 0 < g0 ∧ S = g0 * μ ∧ g0 ∣ H ∧ 0 < μ ∧ x % μ = y % μ := by
  obtain ⟨g0, hgS, hgH, hbez⟩ := gcd_certificate_exists S H
  obtain ⟨μ, hμ⟩ := hgS
  obtain ⟨h', hh'⟩ := hgH
  have hg0 : 0 < g0 := by
    rcases (Arithmetic.zero_le g0).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; rw [← heq, zero_mul] at hμ; exact (ne_of_gt hS) hμ
  have hμ0 : 0 < μ := by
    rcases (Arithmetic.zero_le μ).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; rw [← heq, mul_zero] at hμ; exact (ne_of_gt hS) hμ
  have hb1 : Bez h' μ 1 := by
    obtain ⟨u, v, w, z, he⟩ := hbez
    refine ⟨v, u, z, w, ?_⟩
    rw [hμ, hh'] at he
    have : g0 * (1 + μ * u + h' * v) = g0 * (μ * w + h' * z) := by
      calc g0 * (1 + μ * u + h' * v) = g0 + g0 * μ * u + g0 * h' * v := by ring
        _ = g0 * μ * w + g0 * h' * z := he
        _ = g0 * (μ * w + h' * z) := by ring
    have hc := mul_left_cancel₀ (ne_of_gt hg0) this
    calc 1 + h' * v + μ * u = 1 + μ * u + h' * v := by ring
      _ = μ * w + h' * z := hc
      _ = h' * z + μ * w := by ring
  have h2 : (h' * x) % μ = (h' * y) % μ := by
    rw [hμ, hh', mul_assoc, mul_assoc, ArithmeticModularCancellation.mul_mod_mul hg0 hμ0,
      ArithmeticModularCancellation.mul_mod_mul hg0 hμ0] at h
    exact mul_left_cancel₀ (ne_of_gt hg0) h
  have h3 : μ ∣ h' * absdiff x y := by
    rw [← absdiff_mul]; exact dvd_absdiff_of_mod_eq h2
  have h4 : μ ∣ absdiff x y := unit_certificate_cancel hb1 h3
  refine ⟨g0, μ, hg0, hμ, ⟨h', hh'⟩, hμ0, ?_⟩
  exact ArithmeticAdaptiveFirstDivisibility2011.magnitude_mod (x, y) μ hμ0 h4

/-- A common divisor of `S = 4qY` and `H = 4(XY+Y)+3`, when `q` and `H` are
coprime, divides `3`. -/
theorem gcd_dvd_three (q X Y g0 : V) (hb : Bez q (3 + 4 * (X * Y + Y)) 1)
    (hgS : g0 ∣ 4 * (Y * q)) (hgH : g0 ∣ 3 + 4 * (X * Y + Y)) : g0 ∣ 3 := by
  have hgq : Bez q g0 1 := by
    obtain ⟨h', hh'⟩ := hgH
    obtain ⟨u, v, w, z, he⟩ := hb
    exact ⟨u, h' * v, w, h' * z, by rw [hh'] at he; linear_combination he⟩
  have h3q : g0 ∣ q * 3 := by
    obtain ⟨s, hs⟩ := hgS
    obtain ⟨h', hh'⟩ := hgH
    have e : q * 3 + 4 * (Y * q) * (X + 1) = q * (3 + 4 * (X * Y + Y)) := by ring
    rw [hs, hh'] at e
    refine ⟨q * h' - s * (X + 1), ?_⟩
    rw [mul_tsub, show g0 * (q * h') = q * (g0 * h') by ring,
      show g0 * (s * (X + 1)) = g0 * s * (X + 1) by ring, ← e, add_tsub_cancel_right]
  exact unit_certificate_cancel hgq h3q

end P72Mu

#print axioms P72Mu.betaNat_mod_three
#print axioms P72Mu.beta_cast_mod
#print axioms P72Mu.bez_q_H
#print axioms P72Mu.dvd_absdiff_of_mod_eq
#print axioms P72Mu.gcd_cancel
#print axioms P72Mu.gcd_dvd_three
