import GowersSzemeredi.Proofs05DegreeStep

/-!
# Real-power and rounding budgets for the polynomial degree step

This separates the analytic rounding calculation from the large integer
threshold comparison. With x = r^(1/D), the coarse target is floor(x^(2K)).
Both possible child lengths are controlled, including target minus one.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The real-variable calculation behind the degree step. D is the new
partition constant and K the previous one. -/
theorem polynomial_degree_scale_real (K D d T r v : Nat) (x gamma : Real)
    (hK : 1 ≤ K) (hD : 8 * K ≤ D) (hx : 4 ≤ x)
    (hr : (r : Real) = x ^ D) (hv : (v : Real) ≤ x)
    (hthreshold : 2 * ((T : Real) + 1) ≤ x ^ (2 * K))
    (hgamma : ((2 * K * d + 4 : Nat) : Real) ≤ (D : Real) * gamma) :
    ∃ u : Nat, 1 ≤ u ∧ u ^ 4 ≤ r ∧
      ∀ L : Nat, L = u - 1 ∨ L = u →
        T < L ∧ (v : Real) ≤ (L : Real) ^ (K : Real)⁻¹ ∧
        (u : Real) ^ d * (r : Real) ^ (-gamma) +
          (L : Real) ^ (-(2 * (K : Real)⁻¹)) ≤
          (r : Real) ^ (-(2 * (D : Real)⁻¹)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hK0 : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
  have hD0 : (0 : Real) < D := by exact_mod_cast (show 0 < D by omega)
  have hr0 : (0 : Real) < r := by rw [hr]; positivity
  let y := x ^ (2 * K)
  have hxy : x ≤ y := by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (show 1 ≤ 2 * K by omega)
  have hy4 : 4 ≤ y := hx.trans hxy
  have hy0 : 0 ≤ y := by positivity
  let u := Nat.floor y
  have huupper : (u : Real) ≤ y := Nat.floor_le hy0
  have hufloor : y < (u : Real) + 1 := Nat.lt_floor_add_one y
  have hu : 1 ≤ u := by
    have : (1 : Real) ≤ u := by linarith
    exact_mod_cast this
  have hu4 : u ^ 4 ≤ r := by
    have h : (u : Real) ^ 4 ≤ (r : Real) := by
      calc
        (u : Real) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) huupper _
        _ = x ^ (8 * K) := by dsimp [y]; rw [← pow_mul]; congr 1; omega
        _ ≤ x ^ D := pow_le_pow_right₀ hx1 hD
        _ = r := hr.symm
    exact_mod_cast h
  have herror : (u : Real) ^ d * (r : Real) ^ (-gamma) ≤ 1 / x ^ 4 := by
    have hpower : x ^ (2 * K * d + 4) ≤ (r : Real) ^ gamma := by
      calc
        x ^ (2 * K * d + 4) = x ^ (((2 * K * d + 4 : Nat) : Real)) :=
          (Real.rpow_natCast _ _).symm
        _ ≤ x ^ ((D : Real) * gamma) := Real.rpow_le_rpow_of_exponent_le hx1 hgamma
        _ = (r : Real) ^ gamma := by
          rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    have hnum : (u : Real) ^ d * x ^ 4 ≤ (r : Real) ^ gamma := by
      calc
        (u : Real) ^ d * x ^ 4 ≤ y ^ d * x ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) huupper d) (by positivity)
        _ = x ^ (2 * K * d + 4) := by dsimp [y]; rw [← pow_mul, ← pow_add]
        _ ≤ (r : Real) ^ gamma := hpower
    rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hr0 gamma) (by positivity)).2
    simpa using hnum
  refine ⟨u, hu, hu4, ?_⟩
  intro L hL
  have hLlower : y / 2 ≤ (L : Real) := by
    have huL : (u : Real) - 1 ≤ L := by
      rcases hL with rfl | rfl
      · rw [Nat.cast_sub hu, Nat.cast_one]
      · linarith
    linarith
  have hLpos : (0 : Real) < L := by linarith
  have hTL : T < L := by
    have h : (T : Real) + 1 ≤ L := by change 2 * ((T : Real) + 1) ≤ y at hthreshold; linarith
    have h' : T + 1 ≤ L := by exact_mod_cast h
    omega
  have hxK : 4 ≤ x ^ K := by
    exact hx.trans (by simpa only [pow_one] using pow_le_pow_right₀ hx1 hK)
  have hxKL : x ^ K ≤ (L : Real) := by
    have hy : y = (x ^ K) ^ 2 := by dsimp [y]; rw [← pow_mul]; congr 1; omega
    rw [hy] at hLlower
    nlinarith
  have hvL : (v : Real) ≤ (L : Real) ^ (K : Real)⁻¹ := by
    apply hv.trans
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ x ^ K) hxKL
      (inv_nonneg.mpr hK0.le)
    have hroot : (x ^ K) ^ (K : Real)⁻¹ = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, mul_inv_cancel₀ hK0.ne', Real.rpow_one]
    simpa only [hroot] using h
  let e : Real := 2 * (K : Real)⁻¹
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have he2 : e ≤ 2 := by
    have hK1 : (1 : Real) ≤ K := by exact_mod_cast hK
    have hinv : (K : Real)⁻¹ ≤ 1 := (inv_le_one₀ hK0).2 hK1
    dsimp [e]
    linarith
  have hyPow : y ^ e = x ^ 4 := by
    dsimp only [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    have hexp : ((2 * K : Nat) : Real) * e = 4 := by
      dsimp [e]
      push_cast
      field_simp
      norm_num
    rw [hexp]
    norm_cast
  have htwo : (2 : Real) ^ e ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) he2
    norm_num at h ⊢
    exact h
  have hLpow : x ^ 4 ≤ 4 * (L : Real) ^ e := by
    calc
      x ^ 4 = y ^ e := hyPow.symm
      _ ≤ (2 * (L : Real)) ^ e := Real.rpow_le_rpow hy0 (by linarith) he0
      _ = (2 : Real) ^ e * (L : Real) ^ e := Real.mul_rpow (by norm_num) hLpos.le
      _ ≤ 4 * (L : Real) ^ e := mul_le_mul_of_nonneg_right htwo (by positivity)
  have hdiam : (L : Real) ^ (-e) ≤ 4 / x ^ 4 := by
    rw [Real.rpow_neg hLpos.le, inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hLpos e) (by positivity)).2
    simpa using hLpow
  have hrootD : (r : Real) ^ (2 * (D : Real)⁻¹) = x ^ 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    have h : (D : Real) * (2 * (D : Real)⁻¹) = 2 := by field_simp
    rw [h]
    norm_cast
  refine ⟨hTL, hvL, ?_⟩
  calc
    (u : Real) ^ d * (r : Real) ^ (-gamma) + (L : Real) ^ (-e) ≤
        1 / x ^ 4 + 4 / x ^ 4 := add_le_add herror hdiam
    _ = 5 / x ^ 4 := by ring
    _ ≤ 1 / x ^ 2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [sq_nonneg (x ^ 2 - 5)]
    _ = (r : Real) ^ (-(2 * (D : Real)⁻¹)) := by
      rw [Real.rpow_neg hr0.le, hrootD, inv_eq_one_div]

end LeanProofs.GowersSzemeredi
