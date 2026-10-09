import GowersSzemeredi.Proofs16MonomialControlAbsorption

/-! The variety route's controls give the source's multiple multilinearity at
an explicit parameter.

The ceiling-free controls of `Proofs16VarietyCeilingFreeDecomposition` have,
after `section16_variety_line_factor_power`, the shape
* width exponent `≥ W · (γ/(2r))^(18b) · (ρ/4)^(17+18b)`, and
* graph count `≤ max (81·Q²·7⁴·((2r/γ)^b·(4/ρ)^(1+b))⁴) 27`,

where `b = M·r`, `M = 2^(2^(k+8))`, `r ≥ 1` is the Lemma 16.9 scale, and `W`,
`Q` do not depend on `ρ`. `MultiplyLinearWith.multiplyLinear_of_variety_shape`
shows that such controls are `MultiplyLinear γ s` with
`s = 18r/γ + 64 + L`, for any `L ≥ 0` above `log W⁻¹` and
`log (81·7⁴·Q² + 27)`. The proof applies
`MultiplyLinearWith.multiplyLinear_of_monomial` with exponent
`a = 17 + 18b`; the three lemmas before it carry the algebra. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `log 8 ≥ 2`. -/
theorem two_le_log_eight : (2 : Real) ≤ Real.log 8 := by
  have h8 : Real.exp 2 ≤ 8 := by
    have he := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    nlinarith [Real.exp_pos 1]
  rw [← Real.exp_le_exp, Real.exp_log (by norm_num)]
  exact h8

/-- **The variety graph count in monomial form.** -/
theorem variety_count_le_monomial {X b Q rho : Real} (hX : 1 ≤ X) (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (hr : 0 < rho) (hr1 : rho ≤ 1) :
    max (81 * Q ^ 2 * 7 ^ 4 * (X ^ b * (4 / rho) ^ (1 + b)) ^ 4) 27 ≤
      ((81 * 7 ^ 4 * Q ^ 2 + 27) * (X ^ (4 * b) * (4 : Real) ^ (4 + 4 * b))) *
        rho ^ (-(17 + 18 * b)) := by
  have hX0 : 0 < X := by linarith
  have e1 : (4 / rho) ^ (1 + b) = (4 : Real) ^ (1 + b) * rho ^ (-(1 + b)) := by
    rw [Real.div_rpow (by norm_num) hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
  have e2 : ∀ y : Real, 0 ≤ y → ∀ c : Real, (y ^ c) ^ (4 : Nat) = y ^ (4 * c) := by
    intro y hy c
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num [mul_comm]
  have h1 : (X ^ b * (4 / rho) ^ (1 + b)) ^ 4 =
      X ^ (4 * b) * (4 : Real) ^ (4 + 4 * b) * rho ^ (-(4 + 4 * b)) := by
    rw [e1, mul_pow, mul_pow, e2 X hX0.le, e2 4 (by norm_num), e2 rho hr.le,
      show (4 : Real) * (1 + b) = 4 + 4 * b by ring,
      show (4 : Real) * (-(1 + b)) = -(4 + 4 * b) by ring]
    ring
  have hpow : rho ^ (-(4 + 4 * b)) ≤ rho ^ (-(17 + 18 * b)) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hone : 1 ≤ rho ^ (-(17 + 18 * b)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  have hB0 : 0 ≤ rho ^ (-(4 + 4 * b)) := Real.rpow_nonneg hr.le _
  have hP : 1 ≤ X ^ (4 * b) * (4 : Real) ^ (4 + 4 * b) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hX (by linarith))
      (Real.one_le_rpow (by norm_num) (by linarith))
  rw [h1]
  generalize X ^ (4 * b) * (4 : Real) ^ (4 + 4 * b) = P at hP ⊢
  generalize rho ^ (-(4 + 4 * b)) = B at hpow hB0 ⊢
  generalize rho ^ (-(17 + 18 * b)) = C at hpow hone ⊢
  have hA : 0 ≤ 81 * 7 ^ 4 * Q ^ 2 := by positivity
  have hP0 : 0 ≤ P := by linarith
  have hC0 : 0 ≤ C := by linarith
  apply max_le
  · calc 81 * Q ^ 2 * 7 ^ 4 * (P * B) = (81 * 7 ^ 4 * Q ^ 2) * P * B := by ring
      _ ≤ (81 * 7 ^ 4 * Q ^ 2) * P * C := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (81 * 7 ^ 4 * Q ^ 2 + 27) * P * C := by
          apply mul_le_mul_of_nonneg_right _ hC0
          exact mul_le_mul_of_nonneg_right (by linarith) hP0
  · calc (27 : Real) ≤ 81 * 7 ^ 4 * Q ^ 2 + 27 := by linarith
      _ ≤ (81 * 7 ^ 4 * Q ^ 2 + 27) * P := le_mul_of_one_le_right (by positivity) hP
      _ ≤ (81 * 7 ^ 4 * Q ^ 2 + 27) * P * C := le_mul_of_one_le_right (by positivity) hone

/-- The width control in monomial form. -/
theorem variety_width_monomial {W Y a rho : Real} (hr : 0 < rho) :
    W * Y * (rho / 4) ^ a = (W * Y * (4 : Real) ^ (-a)) * rho ^ a := by
  rw [Real.div_rpow hr.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]
  ring

/-- **The parameter `s = 18r/γ + 64 + L` pays for every loss.** -/
theorem variety_log_budget {M r g L : Real} (hM : 1 ≤ M) (hr : 1 ≤ r) (hg : 0 < g)
    (hg1 : g ≤ 1) (hL : 0 ≤ L) :
    let s := 18 * r / g + 64 + L
    1 ≤ s ∧ 17 + 18 * (M * r) ≤ s * M ∧
      18 * (M * r) * Real.log (8 * r / g) + 2 * (64 + L) ≤ s * M * Real.log s ∧
      2 ≤ Real.log (8 * r / g) := by
  intro s
  have hr0 : 0 < r := by linarith
  have hrg : r ≤ r / g := le_div_self hr0.le hg hg1
  have h8 : 8 ≤ 8 * r / g := by rw [le_div_iff₀ hg]; nlinarith
  have hrg18 : 0 ≤ 18 * r / g := by positivity
  have hs8 : 8 * r / g ≤ s := by
    have : 8 * r / g ≤ 18 * r / g := div_le_div_of_nonneg_right (by nlinarith) hg.le
    show 8 * r / g ≤ 18 * r / g + 64 + L
    linarith
  have hs1 : 1 ≤ s := by linarith
  have hlog8 : Real.log (8 * r / g) ≤ Real.log s := Real.log_le_log (by linarith) hs8
  have hlog8' : 2 ≤ Real.log (8 * r / g) :=
    two_le_log_eight.trans (Real.log_le_log (by norm_num) h8)
  have hlogs : 2 ≤ Real.log s := hlog8'.trans hlog8
  have hsum : s * M = 18 * r / g * M + (64 + L) * M := by show (18 * r / g + 64 + L) * M = _; ring
  have hk : 18 * (M * r) ≤ 18 * r / g * M := by
    rw [show 18 * (M * r) = 18 * M * r by ring, show 18 * r / g * M = 18 * M * (r / g) by ring]
    exact mul_le_mul_of_nonneg_left hrg (by linarith : (0 : Real) ≤ 18 * M)
  refine ⟨hs1, ?_, ?_, hlog8'⟩
  · have : 17 ≤ (64 + L) * M := by nlinarith
    linarith
  · have hA : 18 * (M * r) * Real.log (8 * r / g) ≤ 18 * r / g * M * Real.log s :=
      mul_le_mul hk hlog8 (by linarith) (by positivity)
    have hB : 2 * (64 + L) ≤ (64 + L) * M * Real.log s := by
      have h2 : 2 ≤ M * Real.log s := by nlinarith
      calc 2 * (64 + L) ≤ (64 + L) * (M * Real.log s) :=
            by rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = (64 + L) * M * Real.log s := by ring
    have hsl : s * M * Real.log s = 18 * r / g * M * Real.log s + (64 + L) * M * Real.log s := by
      rw [hsum]; ring
    linarith

/-- **Variety-shaped controls are the source's multiple multilinearity.** -/
theorem MultiplyLinearWith.multiplyLinear_of_variety_shape {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Qb Eb Gamma) {gamma r W Q L : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 1 ≤ r) (hW : 0 < W) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hLW : Real.log W⁻¹ ≤ L) (hLQ : Real.log (81 * 7 ^ 4 * Q ^ 2 + 27) ≤ L)
    (hE : ∀ rho, 0 < rho → rho ≤ 1 →
      W * (gamma / (2 * r)) ^ (18 * (multipleCExponent k * r)) *
        (rho / 4) ^ (17 + 18 * (multipleCExponent k * r)) ≤ Eb rho)
    (hQb : ∀ rho, 0 < rho → rho ≤ 1 →
      Qb rho ≤ max (81 * Q ^ 2 * 7 ^ 4 *
        ((2 * r / gamma) ^ (multipleCExponent k * r) * (4 / rho) ^ (1 + multipleCExponent k * r)) ^ 4)
        27) :
    MultiplyLinear gamma (18 * r / gamma + 64 + L) Gamma := by
  obtain ⟨M, hMe⟩ : ∃ M, multipleCExponent k = M := ⟨_, rfl⟩
  have hM : 1 ≤ M := hMe ▸ one_le_multipleCExponent k
  rw [hMe] at hE hQb
  obtain ⟨hs1, haM, hmain, hlog8⟩ := variety_log_budget hM hr hg hg1 hL
  have hr0 : 0 < r := by linarith
  have hb0 : 0 ≤ M * r := by positivity
  have hRg1 : 1 ≤ 2 * r / gamma := by rw [le_div_iff₀ hg]; nlinarith
  have hRg : 0 < 2 * r / gamma := by linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 4)
    linarith
  have hlog4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsplit : Real.log (2 * r / gamma) + Real.log 4 = Real.log (8 * r / gamma) := by
    rw [← Real.log_mul hRg.ne' (by norm_num)]; congr 1; ring
  have hinv : gamma / (2 * r) = (2 * r / gamma)⁻¹ := by rw [inv_div]
  have hY0 : 0 < (gamma / (2 * r)) ^ (18 * (M * r)) := by positivity
  have hkappa0 : 0 < W * (gamma / (2 * r)) ^ (18 * (M * r)) *
      (4 : Real) ^ (-(17 + 18 * (M * r))) := by positivity
  have hK0 : 0 < (81 * 7 ^ 4 * Q ^ 2 + 27) *
      ((2 * r / gamma) ^ (4 * (M * r)) * (4 : Real) ^ (4 + 4 * (M * r))) := by positivity
  apply h.multiplyLinear_of_monomial hg hg1 hs1 hK0 hkappa0
    (a := 17 + 18 * (M * r))
  · intro rho hrho hrho1
    exact (hQb rho hrho hrho1).trans (variety_count_le_monomial hRg1 hb0 hQ hrho hrho1)
  · intro rho hrho hrho1
    rw [← variety_width_monomial hrho]
    exact hE rho hrho hrho1
  · rw [hMe]; exact haM
  · rw [hMe, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_rpow hRg, Real.log_rpow (by norm_num)]
    have h4 : 4 * (M * r) * Real.log (2 * r / gamma) + (4 + 4 * (M * r)) * Real.log 4 =
        4 * (M * r) * Real.log (8 * r / gamma) + 4 * Real.log 4 := by
      rw [← hsplit]; ring
    have hb8 : 4 * (M * r) * Real.log (8 * r / gamma) ≤ 18 * (M * r) * Real.log (8 * r / gamma) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    calc Real.log (81 * 7 ^ 4 * Q ^ 2 + 27) +
          (4 * (M * r) * Real.log (2 * r / gamma) + (4 + 4 * (M * r)) * Real.log 4)
        = Real.log (81 * 7 ^ 4 * Q ^ 2 + 27) +
          (4 * (M * r) * Real.log (8 * r / gamma) + 4 * Real.log 4) := by rw [h4]
      _ ≤ L + (18 * (M * r) * Real.log (8 * r / gamma) + 12) :=
          add_le_add hLQ (add_le_add hb8 (by linarith))
      _ ≤ (18 * r / gamma + 64 + L) * M * Real.log (18 * r / gamma + 64 + L) := by linarith
  · rw [hMe, Real.log_inv, Real.log_mul (by positivity) (by positivity),
      Real.log_mul hW.ne' hY0.ne', Real.log_rpow (by positivity), Real.log_rpow (by norm_num),
      hinv, Real.log_inv]
    have hW' : -Real.log W ≤ L := by rw [← Real.log_inv]; exact hLW
    have h18 : 18 * (M * r) * Real.log (2 * r / gamma) + (17 + 18 * (M * r)) * Real.log 4 =
        18 * (M * r) * Real.log (8 * r / gamma) + 17 * Real.log 4 := by
      rw [← hsplit]; ring
    linarith

end LeanProofs.GowersSzemeredi
