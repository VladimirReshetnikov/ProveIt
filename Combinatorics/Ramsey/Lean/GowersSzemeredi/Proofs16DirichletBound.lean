import GowersSzemeredi.Proofs16BohrSpectrum

/-! The Dirichlet-kernel bound in `ℤ/N`: the first brick of [49]'s Proposition 26.

Proposition 26 of arXiv:2109.03093 shows that a large Fourier coefficient of a
weakly regular Bohr set lies in a bounded span. Its proof sandwiches the
Bohr indicator between products of trapezoid functions, whose Fourier
coefficients decay like `1/ξ²`. Here that decay is formalized on `ℤ/N`:
* `exponential_eq_exp_valMinAbs`: `e(ξ) = exp(2πi v/N)` with `v` the centered
  representative of `ξ`;
* `norm_one_sub_exponential_ge`: `|1 − e(ξ)| ≥ 4|v|/N`, since
  `|1 − e^{iφ}| = 2|sin(φ/2)|` and `sin x ≥ 2x/π` on `[0, π/2]`;
* `interval_exponential_sum_le`: for `ξ ≠ 0`, the sum of `e(jξ)` over
  `j ∈ [−a, a]` has absolute value at most `N/(2|v|)` (geometric sum). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical Complex

/-- The character in exponential form, via the centered representative. -/
theorem exponential_eq_exp_valMinAbs {N : Nat} [NeZero N] (ξ : ZMod N) :
    exponential ξ = Complex.exp (2 * Real.pi * Complex.I * (ξ.valMinAbs : Complex) / N) := by
  unfold exponential
  conv_lhs => rw [← ZMod.coe_valMinAbs ξ]
  rw [ZMod.stdAddChar_coe]

/-- `|exp(iφ) − 1| = 2|sin(φ/2)|`. -/
theorem norm_exp_I_sub_one (φ : Real) :
    ‖Complex.exp (φ * Complex.I) - 1‖ = 2 * |Real.sin (φ / 2)| := by
  have h1 : Complex.exp (φ * Complex.I) - 1 =
      ((Real.cos φ - 1 : Real) : Complex) + ((Real.sin φ : Real) : Complex) * Complex.I := by
    rw [Complex.exp_mul_I]
    push_cast
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hsq : ‖Complex.exp (φ * Complex.I) - 1‖ ^ 2 = (2 * |Real.sin (φ / 2)|) ^ 2 := by
    rw [h1, Complex.sq_norm, Complex.normSq_add_mul_I]
    have hc : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
      have h2 : Real.cos φ = Real.cos (2 * (φ / 2)) := by ring_nf
      rw [h2, Real.cos_two_mul]
      have := Real.sin_sq_add_cos_sq (φ / 2)
      linarith
    have hs : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
      have h2 : Real.sin φ = Real.sin (2 * (φ / 2)) := by ring_nf
      rw [h2, Real.sin_two_mul]
    have hr : (2 * |Real.sin (φ / 2)|) ^ 2 = 4 * Real.sin (φ / 2) ^ 2 := by
      rw [mul_pow, sq_abs]; norm_num
    rw [hc, hs, hr]
    have := Real.sin_sq_add_cos_sq (φ / 2)
    nlinarith
  have hnn : 0 ≤ 2 * |Real.sin (φ / 2)| := by positivity
  exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).mp hsq

/-- `|sin x| ≥ sin |x|`. -/
theorem abs_sin_ge_sin_abs (x : Real) : Real.sin |x| ≤ |Real.sin x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact le_abs_self _
  · rw [abs_of_neg hx, Real.sin_neg]; exact neg_le_abs _

/-- **The character stays away from `1`.** `|1 − e(ξ)| ≥ 4|v|/N`. -/
theorem norm_one_sub_exponential_ge {N : Nat} [NeZero N] (ξ : ZMod N) :
    4 * |(ξ.valMinAbs : Real)| / N ≤ ‖1 - exponential ξ‖ := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  set v : Real := (ξ.valMinAbs : Real) with hv
  have hexp : exponential ξ = Complex.exp ((2 * Real.pi * v / N : Real) * Complex.I) := by
    rw [exponential_eq_exp_valMinAbs]
    congr 1
    push_cast
    rw [hv]
    push_cast
    ring
  rw [norm_sub_rev, hexp, norm_exp_I_sub_one]
  have hhalf : 2 * Real.pi * v / N / 2 = Real.pi * v / N := by ring
  rw [hhalf]
  -- `|v| ≤ N/2`
  have hvle : |v| ≤ N / 2 := by
    have h := ZMod.natAbs_valMinAbs_le ξ
    have h2 : (ξ.valMinAbs.natAbs : Real) ≤ ((N / 2 : Nat) : Real) := by exact_mod_cast h
    have h3 : ((N / 2 : Nat) : Real) ≤ (N : Real) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : Real) < 2)]
      exact_mod_cast Nat.div_mul_le_self N 2
    have habsv : |v| = ((ξ.valMinAbs.natAbs : Nat) : Real) := by
      rw [hv, Nat.cast_natAbs, Int.cast_abs]
    rw [habsv]
    linarith
  have harg : |Real.pi * v / N| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hNR, div_le_iff₀ hNR]
    have := Real.pi_pos
    nlinarith
  have hsin := Real.mul_le_sin (abs_nonneg (Real.pi * v / N)) harg
  have habs : |Real.pi * v / N| = Real.pi * |v| / N := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hNR]
  rw [habs] at hsin
  have h2 : 2 / Real.pi * (Real.pi * |v| / N) = 2 * |v| / N := by
    field_simp
  rw [h2] at hsin
  have h3 := abs_sin_ge_sin_abs (Real.pi * v / N)
  rw [habs] at h3
  have : 4 * |v| / N = 2 * (2 * |v| / N) := by ring
  rw [this]
  linarith

/-- **Interval sums of characters.** For `ξ ≠ 0`, the sum of `e((c+i)ξ)` over
`i < L` has absolute value at most `N/(2|v|)`. -/
theorem interval_exponential_sum_le {N : Nat} [NeZero N] {ξ : ZMod N} (hξ : ξ ≠ 0)
    (c : ZMod N) (L : Nat) :
    ‖∑ i ∈ Finset.range L, exponential ((c + (i : ZMod N)) * ξ)‖ ≤ N / (2 * |(ξ.valMinAbs : Real)|) := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hv0 : (ξ.valMinAbs : Real) ≠ 0 := by
    have : ξ.valMinAbs ≠ 0 := by rwa [Ne, ZMod.valMinAbs_eq_zero]
    exact_mod_cast this
  have hvpos : 0 < |(ξ.valMinAbs : Real)| := abs_pos.mpr hv0
  set ω := exponential ξ
  have hsplit : ∑ i ∈ Finset.range L, exponential ((c + (i : ZMod N)) * ξ) =
      exponential (c * ξ) * ∑ i ∈ Finset.range L, ω ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_mul, show exponential (c * ξ + (i : ZMod N) * ξ) =
      exponential (c * ξ) * exponential ((i : ZMod N) * ξ) from
      AddChar.map_add_eq_mul ZMod.stdAddChar _ _]
    congr 1
    rw [← nsmul_eq_mul]
    exact AddChar.map_nsmul_eq_pow ZMod.stdAddChar i ξ
  have hnorm1 : ∀ z : ZMod N, ‖exponential z‖ = 1 := fun z => (ZMod.stdAddChar (N := N)).norm_apply z
  have hgeom : (∑ i ∈ Finset.range L, ω ^ i) * (ω - 1) = ω ^ L - 1 := geom_sum_mul ω L
  have hω1 : 0 < ‖ω - 1‖ := by
    have := norm_one_sub_exponential_ge ξ
    rw [norm_sub_rev]
    have : 0 < 4 * |(ξ.valMinAbs : Real)| / N := by positivity
    linarith
  have hnum : ‖ω ^ L - 1‖ ≤ 2 := by
    calc ‖ω ^ L - 1‖ ≤ ‖ω ^ L‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hnorm1, one_pow, norm_one]; norm_num
  have hbound : ‖∑ i ∈ Finset.range L, ω ^ i‖ ≤ 2 / ‖ω - 1‖ := by
    rw [le_div_iff₀ hω1, ← norm_mul, hgeom]
    exact hnum
  have hlow : 4 * |(ξ.valMinAbs : Real)| / N ≤ ‖ω - 1‖ := by
    have := norm_one_sub_exponential_ge ξ
    rwa [norm_sub_rev] at this
  rw [hsplit, norm_mul, hnorm1, one_mul]
  calc ‖∑ i ∈ Finset.range L, ω ^ i‖ ≤ 2 / ‖ω - 1‖ := hbound
    _ ≤ 2 / (4 * |(ξ.valMinAbs : Real)| / N) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hlow
    _ = N / (2 * |(ξ.valMinAbs : Real)|) := by field_simp; ring

end LeanProofs.GowersSzemeredi
