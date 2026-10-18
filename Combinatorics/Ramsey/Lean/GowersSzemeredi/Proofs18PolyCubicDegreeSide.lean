import GowersSzemeredi.Proofs18PolyCubicDegree
import GowersSzemeredi.Proofs18TheoremOneDegreesSide

/-! Declarations of `Proofs18PolyCubicDegree` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- `section18Exponent α k ≤ x` once `x⁻¹ ≤ (2/α)^(2^μ)` with `μ + 1 ≤ 2^(k+10)`. -/
theorem section18Exponent_le_of_inv_le {alpha : Real} (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2)
    {x : Real} (hx : 0 < x) {μ k : Nat} (hμ : μ + 1 ≤ 2 ^ (k + 10))
    (hxinv : x⁻¹ ≤ (2 / alpha) ^ (2 ^ μ)) : section18Exponent alpha k ≤ x := by
  have hαone : alpha ≤ 1 := by linarith only [hα2]
  unfold section18Exponent
  have h1 : alpha ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 10))) ≤ alpha ^ (2 ^ (μ + 1)) :=
    pow_le_pow_of_le_one hα.le hαone (Nat.pow_le_pow_right (by norm_num) hμ)
  have h2 : alpha ^ (2 ^ (μ + 1)) = (alpha ^ 2) ^ (2 ^ μ) := by
    rw [pow_succ, mul_comm (2 ^ μ) 2, pow_mul]
  have h3 : (alpha ^ 2) ^ (2 ^ μ) ≤ (alpha / 2) ^ (2 ^ μ) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith only [hα, hα2]) _
  have h4 : (alpha / 2) ^ (2 ^ μ) = ((2 / alpha) ^ (2 ^ μ))⁻¹ := by rw [← inv_pow, inv_div]
  have h5 : ((2 / alpha) ^ (2 ^ μ))⁻¹ ≤ x := by
    have h := inv_anti₀ (inv_pos.mpr hx) hxinv
    rwa [inv_inv] at h
  calc _ ≤ alpha ^ (2 ^ (μ + 1)) := h1
    _ = (alpha ^ 2) ^ (2 ^ μ) := h2
    _ ≤ (alpha / 2) ^ (2 ^ μ) := h3
    _ = ((2 / alpha) ^ (2 ^ μ))⁻¹ := h4
    _ ≤ x := h5

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.1 from a polynomial envelope** that fits `2^(d+10)`. -/
theorem theorem181At_of_polyEnvBound {d μ : Nat} (h : PolyEnvBound d μ)
    (hμ : μ + 1 ≤ 2 ^ (d + 10)) : Theorem181At d := by
  apply Theorem181At.of_function_discrepancy
  intro alpha ha ha2
  obtain ⟨b, s, T, hB, b0, -, s0, -, bi, si⟩ := h alpha ha ha2
  exact ⟨b, s, T, section18Exponent_le_of_inv_le ha ha2 b0 hμ bi,
    section18Exponent_le_of_inv_le ha ha2 s0 hμ si, hB⟩

/-- **Theorem 18.1 at degree three**, from a polynomial phase partition of
progressions with `K ≤ 2^p` and `p ≤ 2^(2^64)`. -/
theorem theorem_18_1_three_of_phase_partition {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) : Theorem181At 3 := by
  exact theorem181At_of_polyEnvBound
    (polyEnvBound_three_of_phase_partition hpp hp hK hpB) (by norm_num)

end LeanProofs.GowersSzemeredi
