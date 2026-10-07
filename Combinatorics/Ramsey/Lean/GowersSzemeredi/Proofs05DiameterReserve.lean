import GowersSzemeredi.Proofs05Lemma9Induction

/-! Quantitative diameter reserve available before the final weakening in
simultaneous polynomial partitioning. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section5_local_diameter_quarter {x : Real} {t K q : Nat}
    (hx : 1 ≤ x) (hK : 2 ≤ K) (hq : 1 ≤ q)
    (hroot : 16 ≤ x ^ ((K : Real) ^ q)⁻¹) (hlower : x / 4 ≤ t) :
    (t : Real) ^ (-(2 * (K : Real)⁻¹)) ≤ x ^ (-((K : Real) ^ q)⁻¹) / 4 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hK0 : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
  have hKpow : (K : Real) ≤ (K : Real) ^ q := by
    exact le_self_pow₀ (by exact_mod_cast (show 1 ≤ K by omega)) (by omega)
  have hi : ((K : Real) ^ q)⁻¹ ≤ (K : Real)⁻¹ := inv_anti₀ hK0 hKpow
  let u := x ^ (K : Real)⁻¹
  let y := x ^ ((K : Real) ^ q)⁻¹
  have hyu : y ≤ u := Real.rpow_le_rpow_of_exponent_le hx hi
  have hu16 : 16 ≤ u := hroot.trans hyu
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hy0 : 0 < y := by dsimp [y]; positivity
  have ht0 : (0 : Real) < t := (div_pos hx0 (by norm_num)).trans_le hlower
  have he : 0 ≤ 2 * (K : Real)⁻¹ := by positivity
  have he1 : 2 * (K : Real)⁻¹ ≤ 1 := by
    have hK2 : (2 : Real) ≤ K := by exact_mod_cast hK
    simpa only [div_eq_mul_inv] using (div_le_one hK0).mpr hK2
  have hfour : (4 : Real) ^ (2 * (K : Real)⁻¹) ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 4) he1
  have hfour0 : 0 < (4 : Real) ^ (2 * (K : Real)⁻¹) := by positivity
  have hcompose : x ^ (2 * (K : Real)⁻¹) = u ^ 2 := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hlowerpow : u ^ 2 / 4 ≤ (t : Real) ^ (2 * (K : Real)⁻¹) := by
    calc
      _ ≤ u ^ 2 / (4 : Real) ^ (2 * (K : Real)⁻¹) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hfour0 hfour
      _ = (x / 4) ^ (2 * (K : Real)⁻¹) := by
        rw [Real.div_rpow hx0.le (by norm_num), hcompose]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hlower he
  have hscale : 4 * y ≤ (t : Real) ^ (2 * (K : Real)⁻¹) := by
    nlinarith only [hlowerpow, hyu, hu16, hu0]
  rw [Real.rpow_neg ht0.le, Real.rpow_neg hx0.le]
  have hinv := inv_anti₀ (mul_pos (by norm_num : (0 : Real) < 4) hy0) hscale
  simpa only [y, mul_inv_rev, div_eq_mul_inv] using hinv

end LeanProofs.GowersSzemeredi
