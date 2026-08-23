import IntegerPoints.IwaniecMozzochiSection4ExponentPairs

/-!
# Iwaniec--Mozzochi Section 3: the omitted half block

The dyadic Fourier partition used in Section 3 has one block below the
`H = 2^j`, `j : ℕ`, range of (3.2).  At `H = 1 / 2`, the support conditions
force `psiH` to consist of exactly the `h = 1` sine term.  We bound the
corresponding sum with the `(2/7, 4/7)` reciprocal-phase estimate proved from
the Graham--Kolesnik exponent-pair machinery.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

namespace IMHalfBlock

/-- The partition recurrence at its right endpoint forces `chi 2 = 1`. -/
theorem chi_two_eq_one {chi : ℝ → ℝ} (hchi : IsDyadicPartition chi) :
    chi 2 = 1 := by
  have hchi4 : chi 4 = 0 := hchi.2.1 4 le_rfl
  have hrec : chi 2 = 1 - chi (2 * 2) :=
    hchi.2.2.2.1 2 (by norm_num) (by norm_num)
  rw [hrec]
  norm_num [hchi4]

/-- At scale `H = 1 / 2`, only the first Fourier mode survives. -/
theorem psiH_half_eq {chi : ℝ → ℝ} (hchi : IsDyadicPartition chi) (t : ℝ) :
    psiH chi (1 / 2 : ℝ) t = Real.sin (2 * π * t) / π := by
  unfold psiH
  rw [finsum_eq_single _ 1 (fun h hh => by
    by_cases hzero : h = 0
    · subst h
      simp
    · have htwo : 2 ≤ h := by omega
      have htwoReal : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast htwo
      have hfour : (4 : ℝ) ≤ (h : ℝ) / (1 / 2 : ℝ) := by
        calc
          (4 : ℝ) = 2 * 2 := by norm_num
          _ ≤ 2 * (h : ℝ) := mul_le_mul_of_nonneg_left htwoReal (by norm_num)
          _ = (h : ℝ) / (1 / 2 : ℝ) := by ring
      rw [hchi.2.1 _ hfour]
      simp)]
  simp [chi_two_eq_one hchi]

/-- The half block of `deltaHM` is the normalized sine sum with frequency
`h = 1`. -/
theorem deltaHM_half_eq {chi : ℝ → ℝ} (hchi : IsDyadicPartition chi)
    (x M : ℝ) :
    deltaHM chi x (1 / 2 : ℝ) M =
      (∑ m ∈ dyadic M, Real.sin (2 * π * (x / m))) / π := by
  unfold deltaHM
  simp_rw [psiH_half_eq hchi]
  rw [Finset.sum_div]

/-- The imaginary part of `e(t)` is `sin(2 * pi * t)`. -/
theorem e_im (t : ℝ) : (e t).im = Real.sin (2 * π * t) := by
  simp [e, Complex.exp_im]

end IMHalfBlock

/-- The omitted `H = 1 / 2` block satisfies the Iwaniec--Mozzochi target
bound.  Its reciprocal phase has exponent-pair size `x^(2/7)`, which is
smaller than `x^(7/22 + epsilon)` for `x >= 1`. -/
theorem iwaniecMozzochi_halfBlockBound_holds (chi : ℝ → ℝ)
    (hchi : IsDyadicPartition chi) : DeltaHalfHMBound chi theta0 := by
  intro epsilon hepsilon
  obtain ⟨C, hpair⟩ := iwaniecMozzochi_section4_exponentPairBounds_holds
  refine ⟨max C 0 / π, ?_⟩
  intro x M hx hxM hMsqrt
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have htheta : 0 ≤ theta0 := by norm_num [theta0]
  have hMone : 1 ≤ M :=
    (Real.one_le_rpow hx htheta).trans (le_of_lt hxM)
  have hM0 : 0 < M := zero_lt_one.trans_le hMone
  have hMsqrt' : M < Real.sqrt x := by
    simpa only [Real.sqrt_eq_rpow] using hMsqrt
  have hMtwo : M ^ 2 ≤ x := by
    calc
      M ^ 2 ≤ (Real.sqrt x) ^ 2 :=
        (sq_le_sq₀ hM0.le (Real.sqrt_nonneg x)).2 hMsqrt'.le
      _ = x := Real.sq_sqrt hx0
  have hraw :
      ‖∑ m ∈ dyadic M, e (x / m)‖ ≤ C * x ^ ((2 : ℝ) / 7) := by
    simpa only [mul_one] using (hpair x 1 M hMone (by simpa using hMtwo)).2
  have hrawMax :
      ‖∑ m ∈ dyadic M, e (x / m)‖ ≤ max C 0 * x ^ ((2 : ℝ) / 7) := by
    exact hraw.trans <|
      mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hx0 _)
  have himaginary :
      (∑ m ∈ dyadic M, e (x / m)).im =
        ∑ m ∈ dyadic M, Real.sin (2 * π * (x / m)) := by
    simp [IMHalfBlock.e_im]
  have hsine :
      |∑ m ∈ dyadic M, Real.sin (2 * π * (x / m))| ≤
        ‖∑ m ∈ dyadic M, e (x / m)‖ := by
    rw [← himaginary]
    exact Complex.abs_im_le_norm _
  have hexponent : (2 : ℝ) / 7 ≤ theta0 + epsilon := by
    have hstrict : (2 : ℝ) / 7 < theta0 := by norm_num [theta0]
    linarith
  have hrpow : x ^ ((2 : ℝ) / 7) ≤ x ^ (theta0 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hx hexponent
  rw [IMHalfBlock.deltaHM_half_eq hchi, abs_div, abs_of_pos Real.pi_pos]
  calc
    |∑ m ∈ dyadic M, Real.sin (2 * π * (x / m))| / π ≤
        ‖∑ m ∈ dyadic M, e (x / m)‖ / π :=
      (div_le_div_iff_of_pos_right Real.pi_pos).2 hsine
    _ ≤ (max C 0 * x ^ ((2 : ℝ) / 7)) / π :=
      (div_le_div_iff_of_pos_right Real.pi_pos).2 hrawMax
    _ ≤ (max C 0 * x ^ (theta0 + epsilon)) / π :=
      (div_le_div_iff_of_pos_right Real.pi_pos).2 <|
        mul_le_mul_of_nonneg_left hrpow (le_max_right C 0)
    _ = (max C 0 / π) * x ^ (theta0 + epsilon) := by ring

end LeanProofs.IntegerPoints
