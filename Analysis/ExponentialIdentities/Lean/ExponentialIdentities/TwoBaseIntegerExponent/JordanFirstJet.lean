import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.Data.Matrix.Basic

/-!
# Rational Jordan first jets

A square-zero Jordan perturbation of a positive scalar has the formal first-jet value
`b^x I + x b^(x-1) N`.  This file isolates the exact arithmetic implication: if the scalar
value and the nonzero first-jet coefficient are rational, then the exponent is rational; at
base two, an integral scalar value then makes the exponent integral.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- Rationality of a value and its nonzero first derivative recovers the exponent. -/
theorem rational_of_rpow_and_firstJet
    {b : ℕ} (hb : 0 < b) {x : ℝ}
    (hpow : (b : ℝ) ^ x ∈ Set.range ((↑) : ℚ → ℝ))
    (hjet : x * (b : ℝ) ^ (x - 1) ∈ Set.range ((↑) : ℚ → ℝ)) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨q, hq⟩ := hpow
  obtain ⟨r, hr⟩ := hjet
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hq0 : (q : ℝ) ≠ 0 := by
    rw [hq]
    exact ne_of_gt (Real.rpow_pos_of_pos hbR x)
  refine ⟨(b * r) / q, ?_⟩
  rw [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, hq, hr]
  have hsplit : (b : ℝ) ^ x = (b : ℝ) ^ (x - 1) * b := by
    conv_lhs => rw [show x = (x - 1) + 1 by ring]
    exact Real.rpow_add_one (ne_of_gt hbR) (x - 1)
  rw [hsplit]
  field_simp

/-- The explicit first-order functional-calculus value associated with a rational Jordan
direction.  For a square-zero `N`, this is the finite formula used by the Jordan-lift
criterion. -/
def jordanFirstJet {ι : Type*} [DecidableEq ι]
    (b x : ℝ) (N : Matrix ι ι ℚ) : Matrix ι ι ℝ :=
  fun i j ↦ b ^ x * (if i = j then 1 else 0) +
    (x * b ^ (x - 1)) * (N i j : ℝ)

/-- If a nonzero rational Jordan direction has a rational first-jet matrix and the scalar
power is rational, then the derivative coefficient is rational. -/
theorem firstJet_rational_of_jordanFirstJet_rational
    {ι : Type*} [DecidableEq ι] {b x : ℝ} {N : Matrix ι ι ℚ}
    (hN : N ≠ 0)
    (hpow : b ^ x ∈ Set.range ((↑) : ℚ → ℝ))
    (hmat : ∀ i j, jordanFirstJet b x N i j ∈ Set.range ((↑) : ℚ → ℝ)) :
    x * b ^ (x - 1) ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  have hex : ∃ i j, N i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hN
    ext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hex
  obtain ⟨q, hq⟩ := hpow
  obtain ⟨t, ht⟩ := hmat i j
  let δ : ℚ := if i = j then 1 else 0
  refine ⟨(t - q * δ) / N i j, ?_⟩
  rw [Rat.cast_div, Rat.cast_sub, Rat.cast_mul, hq, ht]
  have hδ : (δ : ℝ) = if i = j then 1 else 0 := by
    by_cases h : i = j <;> simp [δ, h]
  rw [hδ]
  simp only [jordanFirstJet]
  have hNijR : (N i j : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hij
  field_simp
  ring

/-- A rational nontrivial Jordan first-jet lift at base two closes the integral-exponent
problem.  This is the kernel-checked arithmetic core of report 20's Jordan criterion. -/
theorem integer_of_two_rpow_integer_of_jordanFirstJet_rational
    {ι : Type*} [DecidableEq ι] {x : ℝ} {N : Matrix ι ι ℚ}
    (hN : N ≠ 0)
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hmat : ∀ i j, jordanFirstJet 2 x N i j ∈ Set.range ((↑) : ℚ → ℝ)) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  have h₂rat : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℚ → ℝ) := by
    obtain ⟨z, hz⟩ := h₂
    refine ⟨z, ?_⟩
    exact_mod_cast hz
  have hjet := firstJet_rational_of_jordanFirstJet_rational hN h₂rat hmat
  have hxrat := rational_of_rpow_and_firstJet (b := 2) (by norm_num) h₂rat hjet
  exact LeanProofs.IntegerExponent.integer_of_rational_of_two_rpow_integer hxrat h₂

end

end LeanProofs.TwoBaseIntegerExponent
