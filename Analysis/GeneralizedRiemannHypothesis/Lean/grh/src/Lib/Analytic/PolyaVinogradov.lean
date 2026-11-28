import Lib.Analytic.ZeroSymmetry

/-!
# Gauss sums of primitive characters and the Pólya–Vinogradov bound

The Gauss sum of a primitive Dirichlet character mod `q` has absolute value `√q`. For a
non-principal character mod `q`, every partial sum of its values is at most `2 √q (1 + log q)` in
absolute value.

* `New.norm_gaussSum_of_isPrimitive`: the modulus of the Gauss sum.
* `New.polya_vinogradov`: the Pólya–Vinogradov inequality.

## Relation to the literature

Known result: the Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character. It is
proved here for initial intervals only, with the explicit bound `2 √q (1 + log q)`. The case of a
general character is reduced to the primitive character that induces it by a Möbius sieve. Source:
Pólya 1918, Vinogradov 1918; Davenport, Multiplicative Number Theory; Montgomery–Vaughan Thm 9.18.
-/

open Complex Finset DirichletCharacter Real ZMod ArithmeticFunction Moebius NeZero Nat

namespace New

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The Gauss sum of a primitive Dirichlet character mod `q`, taken with the standard additive
character `x ↦ exp (2 π i x / q)` of `ZMod q`, has absolute value `√q`. -/
lemma norm_gaussSum_of_isPrimitive (hχ : χ.IsPrimitive) : ‖gaussSum χ stdAddChar‖ = √q := by
  -- Fourier inversion at `-1`: the Gauss sum times its complex conjugate is `q`.
  have h_dft : dft (χ : ZMod q → ℂ) = fun k : ZMod q ↦ χ⁻¹ (-k) * gaussSum χ stdAddChar :=
    funext hχ.fourierTransform_eq_inv_mul_gaussSum
  have h_inversion : dft (dft (χ : ZMod q → ℂ)) (-1) = q := by simp [dft_dft]
  have h_conj : star (gaussSum χ stdAddChar) * gaussSum χ stdAddChar = q := by
    rw [← h_inversion, h_dft, dft_mul_const, dft_comp_neg, star_gaussSum_eq]
    simp [fourierTransform_eq_gaussSum_mulShift, ← AddChar.inv_mulShift]
  have h_sq : ‖gaussSum χ stdAddChar‖ * ‖gaussSum χ stdAddChar‖ = q := by
    simpa using congrArg norm h_conj
  rw [← h_sq, Real.sqrt_mul_self (norm_nonneg _)]

/-- The chord from `1` to the root of unity `stdAddChar k = exp (2 π i x)`, where `x = k / q` lies
in `[0, 1]`, has length at least `4 x (1 - x)`. -/
lemma four_mul_le_norm_stdAddChar_sub_one {k : ZMod q} {x : ℝ} (hx : (k.val : ℝ) = q * x)
    (hx_nonneg : 0 ≤ x) (hx_le : x ≤ 1) : 4 * (x * (1 - x)) ≤ ‖stdAddChar k - 1‖ := by
  -- With `y = π x / 2` the chord has length `2 sin (2 y) = 4 sin y cos y`, where `sin y ≥ x` and
  -- `cos y ≥ 1 - x` by concavity.
  have h_sin : x ≤ Real.sin (π / 2 * x) := le_sin_mul hx_nonneg hx_le
  have h_cos : 1 - x ≤ Real.cos (π / 2 * x) := by
    simpa [field] using
      one_sub_mul_le_cos (by positivity) (mul_le_of_le_one_right pi_div_two_pos.le hx_le)
  have h_angle : 2 * π * (q * x / q) / 2 = 2 * (π / 2 * x) := by field [NeZero.ne]
  calc 4 * (x * (1 - x))
      ≤ 4 * (Real.sin (π / 2 * x) * Real.cos (π / 2 * x)) := by nlinarith
    _ = 2 * Real.sin (2 * (π / 2 * x)) := by linear_combination -2 * Real.sin_two_mul (π / 2 * x)
    _ ≤ ‖stdAddChar k - 1‖ := by
        rw [stdAddChar_apply, toCircle_eq_circleExp, Circle.coe_exp, mul_comm _ I, hx,
          norm_exp_I_mul_ofReal_sub_one, h_angle]
        exact le_norm_self _

/-- For `k ≠ 0` in `ZMod q`, the sum of the powers `1, …, X` of the root of unity
`stdAddChar k = exp (2 π i k / q)` has absolute value at most `q / 2 · (1 / k + 1 / (q - k))`,
where `k` is read as its representative `k.val` in `[1, q - 1]`. -/
lemma norm_sum_stdAddChar_pow_le {k : ZMod q} (hk : k ≠ 0) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, stdAddChar k ^ v‖ ≤
      q / 2 * ((k.val : ℝ)⁻¹ + ((q - k.val : ℕ) : ℝ)⁻¹) := by
  have hq_pos : (0 : ℝ) < q := mod_cast NeZero.pos q
  let x : ℝ := k.val / q
  have hx : (k.val : ℝ) = q * x := (mul_div_cancel₀ _ hq_pos.ne').symm
  have hx_pos : 0 < x := div_pos (mod_cast val_pos.mpr hk) hq_pos
  have hx_lt : x < 1 := (div_lt_one hq_pos).mpr (mod_cast k.val_lt)
  have h_sub_pos : 0 < 1 - x := sub_pos.mpr hx_lt
  have h_ne : stdAddChar k ≠ 1 := by simpa using injective_stdAddChar.ne hk
  calc ‖∑ v ∈ Ioc 0 X, stdAddChar k ^ v‖
      = ‖stdAddChar k ^ (X + 1) - stdAddChar k ^ 1‖ / ‖stdAddChar k - 1‖ := by
        rw [← Ico_add_one_add_one_eq_Ioc, zero_add, geom_sum_Ico h_ne (Nat.le_add_left 1 X),
          norm_div]
    _ ≤ (1 + 1) / (4 * (x * (1 - x))) := by
        grw [norm_sub_le, ← four_mul_le_norm_stdAddChar_sub_one hx hx_pos.le hx_lt.le]
        simp [norm_pow, AddChar.norm_apply]
    _ = q / 2 * ((k.val : ℝ)⁻¹ + ((q - k.val : ℕ) : ℝ)⁻¹) := by
        rw [Nat.cast_sub (val_le k), hx]
        field_simp
        ring

/-- The Pólya–Vinogradov inequality for a primitive Dirichlet character `χ` of modulus `q ≠ 1`:
`|∑_{1 ≤ v ≤ X} χ v| ≤ √q (1 + log q)` for all `X`. -/
lemma norm_sum_le_of_isPrimitive (hχ : χ.IsPrimitive) (hq : q ≠ 1) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ √q * (1 + Real.log q) := by
  -- Fourier inversion; the Fourier coefficients of `χ` are `χ⁻¹ (-k)` times the Gauss sum.
  have h_expand : ∑ v ∈ Ioc 0 X, χ v = (q : ℂ)⁻¹ * ∑ k : ZMod q,
      (∑ v ∈ Ioc 0 X, stdAddChar k ^ v) * (χ⁻¹ (-k) * gaussSum χ stdAddChar) := by
    conv_lhs => rw [← dft.symm_apply_apply χ]
    simp_rw [invDFT_apply, ← nsmul_eq_mul', AddChar.map_nsmul_eq_pow, ← smul_sum,
      sum_comm (s := Ioc 0 X), ← sum_smul, hχ.fourierTransform_eq_inv_mul_gaussSum, smul_eq_mul]
  -- The term `k = 0` vanishes, and the bounds `f k` of the others add up to twice a harmonic sum
  -- (the terms `0⁻¹ = 0` do no harm).
  let f (n : ℕ) : ℝ := √q * q / 2 * ((n : ℝ)⁻¹ + ((q - n : ℕ) : ℝ)⁻¹)
  have h_term (k : ZMod q) (hk : k ∈ univ.erase 0) :
      ‖(∑ v ∈ Ioc 0 X, stdAddChar k ^ v) * (χ⁻¹ (-k) * gaussSum χ stdAddChar)‖ ≤ f k.val := by
    grw [norm_mul, norm_mul, norm_le_one, norm_gaussSum_of_isPrimitive hχ,
      norm_sum_stdAddChar_pow_le (ne_of_mem_erase hk)]
    exact le_of_eq (by ring)
  have h_subset : ((univ : Finset (ZMod q)).erase 0).image ZMod.val ⊆ range (q + 1) :=
    image_subset_iff.mpr fun k _ ↦ mem_range.mpr (Nat.lt_succ_of_lt k.val_lt)
  have h_harmonic : ∑ n ∈ range (q + 1), (n : ℝ)⁻¹ = harmonic q := by
    simp [harmonic, sum_range_succ']
  calc ‖∑ v ∈ Ioc 0 X, χ v‖
      ≤ (q : ℝ)⁻¹ * ∑ k ∈ (univ : Finset (ZMod q)).erase 0, f k.val := by
        grw [h_expand, ← sum_erase _ (a := 0) (by simp [map_zero' χ⁻¹ hq]), norm_mul,
          norm_sum_le_of_le _ h_term]
        simp
    _ ≤ (q : ℝ)⁻¹ * ∑ n ∈ range (q + 1), f n := by
        rw [← sum_image (val_injective q).injOn]
        gcongr
    _ = √q * harmonic q := by
        rw [← mul_sum, sum_add_distrib, sum_flip fun n : ℕ ↦ (n : ℝ)⁻¹, h_harmonic]
        field [NeZero.ne]
    _ ≤ √q * (1 + Real.log q) := by grw [harmonic_le_one_add_log]

/-- A natural number `r` has at most `2 √r` divisors. -/
lemma card_divisors_le_two_mul_sqrt (r : ℕ) : (#r.divisors : ℝ) ≤ 2 * √r := by
  -- Of two complementary divisors one is at most `√r`.
  have h_sub : r.divisors ⊆ Ioc 0 r.sqrt ∪ (Ioc 0 r.sqrt).image fun d : ℕ ↦ r / d := by
    intro d hd
    obtain ⟨⟨e, rfl⟩, hr⟩ : d ∣ r ∧ r ≠ 0 := mem_divisors.mp hd
    obtain ⟨hd_pos, he_pos⟩ : 0 < d ∧ 0 < e := by simpa [Nat.pos_iff_ne_zero] using hr
    rcases le_sqrt_of_eq_mul (rfl : d * e = d * e) with hd_le | he_le
    · simp [hd_pos, hd_le]
    · exact mem_union_right _
        (mem_image.mpr ⟨e, mem_Ioc.mpr ⟨he_pos, he_le⟩, Nat.mul_div_cancel d he_pos⟩)
  grw [card_le_card h_sub, card_union_le, Finset.card_image_le, ← nat_sqrt_le_real_sqrt]
  simp [two_mul]

omit [NeZero q] in
/-- Möbius sieve: if `χ` mod `q = M * r` is induced by `ψ` mod `M`, then `χ v` is the sum of
`μ d • ψ v` over the common divisors `d` of `v` and `r`. -/
lemma apply_eq_sum_moebius_smul_of_changeLevel_eq {M r : ℕ} {ψ : DirichletCharacter ℂ M}
    (hr : q = M * r) (h_ind : changeLevel ⟨r, hr⟩ ψ = χ) (v : ℕ) :
    χ v = ∑ d ∈ (v.gcd r).divisors, μ d • ψ v := by
  -- The sum of `μ` over the divisors of `n` is `1` for `n = 1` and `0` otherwise.
  rw [← sum_smul, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
  show χ v = (if v.gcd r = 1 then 1 else 0 : ℤ) • ψ v
  have h_coprime : IsCoprime (v : ℤ) q ↔ IsCoprime (v : ℤ) M ∧ v.gcd r = 1 := by
    simp only [isCoprime_iff_coprime, hr, coprime_mul_iff_right, ← coprime_iff_gcd_eq_one]
  by_cases hv : IsCoprime (v : ℤ) q
  · have h_eq : χ v = ψ v := by simpa [h_ind] using ψ.changeLevel_eq_cast_of_dvd' ⟨r, hr⟩ hv
    simp [h_eq, (h_coprime.mp hv).2]
  · have hχ_zero : χ v = 0 := by simpa using (χ.apply_eq_zero_iff v).mpr hv
    split_ifs with h_gcd
    · simpa [hχ_zero] using
        ((ψ.apply_eq_zero_iff v).mpr fun h ↦ hv (h_coprime.mpr ⟨h, h_gcd⟩)).symm
    · rw [hχ_zero, zero_smul]

/-- The multiples of `d > 0` in `[1, X]` are the numbers `d * e` with `1 ≤ e ≤ X / d`. -/
lemma filter_dvd_Ioc_eq_image_mul {d : ℕ} (hd : 0 < d) (X : ℕ) :
    {v ∈ Ioc 0 X | d ∣ v} = (Ioc 0 (X / d)).image fun e : ℕ ↦ d * e := by
  ext v
  simp only [mem_filter, mem_image, mem_Ioc, le_div_iff_mul_le hd, mul_comm _ d, dvd_def]
  aesop

/-- If `χ` mod `q = M * r` is induced by `ψ` mod `M`, then a partial sum of `χ` is a combination of
partial sums of `ψ`, indexed by the divisors `d` of `r`, with coefficients `μ d * ψ d`. -/
lemma sum_eq_sum_divisors_of_changeLevel_eq {M r : ℕ} {ψ : DirichletCharacter ℂ M}
    (hr : q = M * r) (h_ind : changeLevel ⟨r, hr⟩ ψ = χ) (X : ℕ) :
    ∑ v ∈ Ioc 0 X, χ v = ∑ d ∈ r.divisors, μ d * ψ d * ∑ v ∈ Ioc 0 (X / d), ψ v := by
  have hr0 : r ≠ 0 := right_ne_zero_of_mul (hr.symm.trans_ne (NeZero.ne q))
  -- Swap the sums and write `v = d * e` with `1 ≤ e ≤ X / d`.
  have h_gcd (v : ℕ) : (v.gcd r).divisors = {d ∈ r.divisors | d ∣ v} := by
    grind [Nat.dvd_gcd_iff]
  calc ∑ v ∈ Ioc 0 X, χ v
      = ∑ v ∈ Ioc 0 X, ∑ d ∈ r.divisors with d ∣ v, μ d • ψ v := by
        simp only [apply_eq_sum_moebius_smul_of_changeLevel_eq hr h_ind, h_gcd]
    _ = ∑ d ∈ r.divisors, ∑ v ∈ Ioc 0 X with d ∣ v, μ d • ψ v := by
        simp only [sum_filter, sum_comm (s := Ioc 0 X)]
    _ = ∑ d ∈ r.divisors, μ d * ψ d * ∑ v ∈ Ioc 0 (X / d), ψ v := by
        refine sum_congr rfl fun d hd ↦ ?_
        rw [filter_dvd_Ioc_eq_image_mul (pos_of_mem_divisors hd)]
        simp [mul_sum, mul_assoc, (pos_of_mem_divisors hd).ne']

/-- The **Pólya–Vinogradov inequality** for initial intervals: for a non-principal Dirichlet
character `χ` mod `q` one has `|∑_{1 ≤ v ≤ X} χ v| ≤ 2 √q (1 + log q)` for all `X`. -/
theorem polya_vinogradov (hχ : χ ≠ 1) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ 2 * √q * (1 + Real.log q) := by
  -- Apply the bound for the primitive `ψ` mod `M` that induces `χ`, once for each divisor of
  -- `r = q / M`.
  obtain ⟨M, hMq, ψ, _, hψ, h_ind⟩ := exists_isPrimitive_changeLevel_eq χ
  obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd hMq
  have hM : M ≠ 1 := fun h ↦ hχ (by rw [← h_ind, ψ.level_one' h, map_one])
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have hM_le : (M : ℝ) ≤ q := mod_cast le_of_dvd (NeZero.pos q) hMq
  have h_term (d : ℕ) : ‖μ d * ψ d * ∑ v ∈ Ioc 0 (X / d), ψ v‖ ≤ √M * (1 + Real.log q) := by
    have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by simpa using mod_cast abs_moebius_le_one (n := d)
    grw [norm_mul, norm_mul, hμ, ψ.norm_le_one, norm_sum_le_of_isPrimitive hψ hM, one_mul,
      one_mul, Real.log_le_log hM_pos hM_le]
  calc ‖∑ v ∈ Ioc 0 X, χ v‖
      ≤ #r.divisors • (√M * (1 + Real.log q)) := by
        grw [sum_eq_sum_divisors_of_changeLevel_eq hr h_ind, norm_sum_le]
        exact sum_le_card_nsmul _ _ _ fun (d : ℕ) _ ↦ h_term d
    _ ≤ 2 * √r * (√M * (1 + Real.log q)) := by
        grw [nsmul_eq_mul, card_divisors_le_two_mul_sqrt]
    _ = 2 * √q * (1 + Real.log q) := by
        rw [hr, Nat.cast_mul, Real.sqrt_mul hM_pos.le]
        ring

end New
