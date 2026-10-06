import GowersSzemeredi.Proofs05MultilinearStep

/-! # Upward rounding budgets for the multilinear height induction -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Choose a coarse target one above ceil(x), so target-minus-one is at least
x. The stronger recurrence exponent pays for the upper-rounding factor. -/
theorem multilinear_height_rounding (K k h T r : Nat) (x gamma : Real)
    (hK : 8 ≤ K) (hk : 1 ≤ k) (hx : 2 ≤ x)
    (hr : (r : Real) = x ^ K) (hT : (T : Real) ≤ x)
    (hgamma : (4 * k : Nat) ≤ (K : Real) * gamma) :
    ∃ u : Nat, 2 ≤ u ∧ u ^ 4 ≤ r ∧ T ≤ u - 1 ∧
      (r : Real) ^ (((K : Real) ^ (h + 1))⁻¹) ≤
        ((u - 1 : Nat) : Real) ^ (((K : Real) ^ h)⁻¹) ∧
      ((u - 1 : Nat) : Real) ^ (-((K : Real) ^ h)⁻¹) ≤
        (r : Real) ^ (-((K : Real) ^ (h + 1))⁻¹) ∧
      (u : Real) ^ k * (r : Real) ^ (-gamma) ≤
        (2 : Real) ^ (-(k : Real)) * (r : Real) ^ (-((K : Real) ^ (h + 1))⁻¹) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hK0 : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
  have hr0 : (0 : Real) < r := by rw [hr]; positivity
  let L := Nat.ceil x
  let u := L + 1
  have hL : x ≤ (L : Real) := Nat.le_ceil x
  have hLupper : (L : Real) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hL2 : 2 ≤ L := by exact_mod_cast hx.trans hL
  have hu : 2 ≤ u := by dsimp [u]; omega
  have hupred : u - 1 = L := by dsimp [u]
  have huupper : (u : Real) ≤ 2 * x := by dsimp [u]; push_cast; linarith
  have hu4 : u ^ 4 ≤ r := by
    have htwo : (2 : Real) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx 4
    have h : (u : Real) ^ 4 ≤ (r : Real) := by
      calc
        (u : Real) ^ 4 ≤ (2 * x) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) huupper 4
        _ = (2 : Real) ^ 4 * x ^ 4 := mul_pow _ _ _
        _ ≤ x ^ 4 * x ^ 4 := mul_le_mul_of_nonneg_right htwo (by positivity)
        _ = x ^ 8 := by ring
        _ ≤ x ^ K := pow_le_pow_right₀ hx1 hK
        _ = r := hr.symm
    exact_mod_cast h
  have hthreshold : T ≤ L := by exact_mod_cast hT.trans hL
  have hroot : (r : Real) ^ (((K : Real) ^ (h + 1))⁻¹) =
      x ^ (((K : Real) ^ h)⁻¹) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    rw [pow_succ]
    field_simp
  have hwidth : (r : Real) ^ (((K : Real) ^ (h + 1))⁻¹) ≤
      (L : Real) ^ (((K : Real) ^ h)⁻¹) := by
    rw [hroot]
    exact Real.rpow_le_rpow hx0.le hL (by positivity)
  have hL0 : (0 : Real) < L := hx0.trans_le hL
  have hdiam : (L : Real) ^ (-((K : Real) ^ h)⁻¹) ≤
      (r : Real) ^ (-((K : Real) ^ (h + 1))⁻¹) := by
    rw [Real.rpow_neg hL0.le, Real.rpow_neg hr0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hr0 _) hwidth
  have hKpow : (1 : Real) ≤ (K : Real) ^ h :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ K by omega))
  have hinv : ((K : Real) ^ h)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hKpow
  have hsmallRoot : (r : Real) ^ (((K : Real) ^ (h + 1))⁻¹) ≤ x := by
    rw [hroot]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 hinv
  have hrecip : 1 / x ≤ (r : Real) ^ (-((K : Real) ^ (h + 1))⁻¹) := by
    rw [Real.rpow_neg hr0.le]
    simpa only [one_div] using inv_anti₀ (Real.rpow_pos_of_pos hr0 _) hsmallRoot
  have hpower : x ^ (4 * k) ≤ (r : Real) ^ gamma := by
    calc
      x ^ (4 * k) = x ^ ((4 * k : Nat) : Real) := (Real.rpow_natCast _ _).symm
      _ ≤ x ^ ((K : Real) * gamma) := Real.rpow_le_rpow_of_exponent_le hx1 hgamma
      _ = (r : Real) ^ gamma := by rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
  have hnum : (u : Real) ^ k * (2 : Real) ^ k * x ≤ (r : Real) ^ gamma := by
    calc
      (u : Real) ^ k * (2 : Real) ^ k * x ≤ (2 * x) ^ k * (2 : Real) ^ k * x := by
        gcongr
      _ ≤ (x * x) ^ k * x ^ k * x := by gcongr
      _ = x ^ (3 * k + 1) := by rw [mul_pow, ← pow_add, ← pow_add, ← pow_succ]; congr 1; omega
      _ ≤ x ^ (4 * k) := pow_le_pow_right₀ hx1 (by omega)
      _ ≤ (r : Real) ^ gamma := hpower
  have herror : (u : Real) ^ k * (r : Real) ^ (-gamma) ≤
      (2 : Real) ^ (-(k : Real)) * (1 / x) := by
    rw [Real.rpow_neg hr0.le, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_natCast]
    have hden : (0 : Real) < (r : Real) ^ gamma := Real.rpow_pos_of_pos hr0 _
    have htwo : (0 : Real) < (2 : Real) ^ k := by positivity
    apply (mul_le_mul_iff_of_pos_right (show 0 < (r : Real) ^ gamma * ((2 : Real) ^ k * x) by positivity)).mp
    field_simp
    exact hnum
  refine ⟨u, hu, hu4, ?_, ?_, ?_, ?_⟩
  · simpa only [hupred] using hthreshold
  · simpa only [hupred] using hwidth
  · simpa only [hupred] using hdiam
  · exact herror.trans (mul_le_mul_of_nonneg_left hrecip (by positivity))

end LeanProofs.GowersSzemeredi
