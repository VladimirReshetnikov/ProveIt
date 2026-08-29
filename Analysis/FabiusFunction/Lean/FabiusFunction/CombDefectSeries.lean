import FabiusFunction.CombFirstDefect

/-!
# The defect Fourier series of the shifted monomial combs

The spectral display of `CombFirstDefect` writes the comb as its
Fourier series.  This module subtracts the zero mode: for *every*
degree, mesh, and shift, the quadrature defect is the sum of the
nonzero-frequency aliases,

`∑_k (θ+k)^p·up((θ+k)/M) - ∫ x^p·up(x/M) dx
  = ∑_{ℓ≠0} 𝓕f(ℓ)·e^{2πiℓθ}`,

absolutely summably — the Schwartz decay of the transform gives the
`|ℓ|^{-2}` bound with no case analysis.  At the threshold degree
`p = v₂(M)+1` the even frequencies die by the sharp valuation count,
so the defect is carried by the odd frequencies alone — the odd-level
defect series of the comb volume's spectral-Dirichlet layer, whose
coefficients are the exact first-defect values.
-/

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- The Fourier side of the comb's spectral display is absolutely
summable: Schwartz decay of the transform. -/
theorem summable_fourier_monomialRvachevSchwartz (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) (p : ℕ) (θ : ℝ) :
    Summable (fun ℓ : ℤ =>
      𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ *
        fourier ℓ (θ : UnitAddCircle)) := by
  obtain ⟨C, hCpos, hC⟩ :=
    (𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
      (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))).decay 2 0
  refine Summable.of_norm_bounded_eventually
    (g := fun ℓ : ℤ => C * |(ℓ : ℝ)| ^ (-(2 : ℝ)))
    ((summable_abs_int_rpow one_lt_two).mul_left C) ?_
  refine Filter.eventually_cofinite.mpr
    (Set.Finite.subset (Set.finite_singleton (0 : ℤ)) fun ℓ hℓ => ?_)
  simp only [Set.mem_setOf_eq, not_le] at hℓ
  by_contra hne0
  rw [Set.mem_singleton_iff] at hne0
  have hℓabs : (0 : ℝ) < |(ℓ : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr hne0)
  have hfle : ‖(fourier ℓ) (θ : UnitAddCircle)‖ ≤ 1 := by
    haveI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
    calc ‖(fourier ℓ) (θ : UnitAddCircle)‖
        ≤ ‖fourier (T := 1) ℓ‖ := ContinuousMap.norm_coe_le_norm _ _
      _ = 1 := fourier_norm ℓ
  have hdecay := hC ((ℓ : ℤ) : ℝ)
  rw [norm_iteratedFDeriv_zero] at hdecay
  have hrpow : |(ℓ : ℝ)| ^ (-(2 : ℝ)) = (|(ℓ : ℝ)| ^ (2 : ℕ))⁻¹ := by
    rw [← Real.rpow_natCast |(ℓ : ℝ)| 2,
      ← Real.rpow_neg (abs_nonneg _)]
    norm_num
  have hsq : (0 : ℝ) < |(ℓ : ℝ)| ^ (2 : ℕ) := by positivity
  have hcoeff : ‖𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
      (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ((ℓ : ℤ) : ℝ)‖ ≤
      C * |(ℓ : ℝ)| ^ (-(2 : ℝ)) := by
    rw [hrpow, ← division_def, le_div_iff₀ hsq]
    calc ‖𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ((ℓ : ℤ) : ℝ)‖ *
          |(ℓ : ℝ)| ^ (2 : ℕ)
        = ‖((ℓ : ℤ) : ℝ)‖ ^ 2 *
            ‖𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
              (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))
              ((ℓ : ℤ) : ℝ)‖ := by
          rw [Real.norm_eq_abs]
          ring
      _ ≤ C := hdecay
  have hterm : ‖𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
      (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ *
      fourier ℓ (θ : UnitAddCircle)‖ ≤
      C * |(ℓ : ℝ)| ^ (-(2 : ℝ)) := by
    rw [norm_mul]
    calc ‖𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ‖ *
          ‖(fourier ℓ) (θ : UnitAddCircle)‖
        ≤ (C * |(ℓ : ℝ)| ^ (-(2 : ℝ))) * 1 :=
          mul_le_mul hcoeff hfle (norm_nonneg _) (by positivity)
      _ = C * |(ℓ : ℝ)| ^ (-(2 : ℝ)) := mul_one _
  exact absurd hterm (not_le.mpr hℓ)

/-- **The defect Fourier series**: for every degree, mesh, and shift,
the quadrature defect is the absolutely convergent sum of the
nonzero-frequency aliases. -/
theorem tsum_shifted_monomial_sub_integral (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) (p : ℕ) (θ : ℝ) :
    (∑' k : ℤ, monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
        (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (θ + k)) -
      ∫ x : ℝ, ((x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) =
      ∑' ℓ : ℤ, if ℓ = (0 : ℤ) then 0 else
        𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
            (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ *
          fourier ℓ (θ : UnitAddCircle) := by
  rw [tsum_shifted_monomial_eq_tsum_fourier F hF hM p θ,
    (summable_fourier_monomialRvachevSchwartz F hF hM p
      θ).tsum_eq_add_tsum_ite (0 : ℤ)]
  have h0 : 𝓕 (monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
      (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) (((0 : ℤ) : ℝ)) *
      fourier (0 : ℤ) (θ : UnitAddCircle) =
      ∫ x : ℝ, ((x ^ p * rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := by
    rw [fourier_zero, mul_one]
    show 𝓕 (⇑(monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
      (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))) (((0 : ℤ) : ℝ)) = _
    rw [Int.cast_zero]
    exact fourier_monomialRvachevSchwartz_nat_zero F hF hM p
  rw [h0]
  ring

/-- **The odd-level defect series**: at the threshold degree
`p = v₂(M)+1` the surviving aliases sit at the odd frequencies alone
— their coefficients are the exact first-defect values. -/
theorem tsum_shifted_monomial_sub_integral_odd (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) (θ : ℝ) :
    (∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (θ + k)) -
      ∫ x : ℝ, ((x ^ (padicValNat 2 M + 1) *
        rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) =
      ∑' ℓ : ℤ, if Odd ℓ then
        𝓕 (monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
            ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ *
          fourier ℓ (θ : UnitAddCircle)
        else 0 := by
  rw [tsum_shifted_monomial_sub_integral F hF hM
    (padicValNat 2 M + 1) θ]
  refine tsum_congr fun ℓ => ?_
  by_cases h0 : ℓ = 0
  · subst h0
    rw [if_pos rfl, if_neg (by simp [Int.odd_iff] : ¬ Odd (0 : ℤ))]
  · rw [if_neg h0]
    by_cases hodd : Odd ℓ
    · rw [if_pos hodd]
    · rw [if_neg hodd]
      have h2 : (2 : ℤ) ∣ ℓ := (Int.not_odd_iff_even.mp hodd).two_dvd
      have h2n : 2 ∣ ℓ.natAbs := by
        have h := Int.natAbs_dvd_natAbs.mpr h2
        simpa using h
      have hpos : 0 < padicValNat 2 ℓ.natAbs := by
        rw [← Nat.factorization_def _ Nat.prime_two]
        exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two
          (Int.natAbs_ne_zero.mpr h0) h2n
      have hz : 𝓕 (⇑(monomialRvachevSchwartz F hF
          (padicValNat 2 M + 1) ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))) ((ℓ : ℤ) : ℝ) = 0 :=
        fourier_monomialRvachevSchwartz_nat_int_eq_zero_of_le F hF hM
          h0 (by omega)
      calc 𝓕 (monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
            ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ *
            fourier ℓ (θ : UnitAddCircle)
          = 𝓕 (⇑(monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
              ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))))
              ((ℓ : ℤ) : ℝ) *
            fourier ℓ (θ : UnitAddCircle) := rfl
        _ = 0 := by rw [hz, zero_mul]

private theorem neg_pow_ofReal_mul (v r : ℝ) (p : ℕ) :
    (((-v) ^ p * r : ℝ) : ℂ) =
      (-1 : ℂ) ^ p * ((v ^ p * r : ℝ) : ℂ) := by
  rw [neg_pow]
  push_cast
  ring

/-- **Coefficient parity**: the transform of the degree-`p` sample
function has the parity of `p` — the up-factor is even, so
`𝓕f(-w) = (-1)^p·𝓕f(w)`.  Combined with the spectral display this
pairs the `±ℓ` aliases: at even degree they reinforce, at odd degree
they cancel at the endpoint phase. -/
theorem fourier_monomialRvachevSchwartz_neg (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) (p : ℕ) (w : ℝ) :
    𝓕 (⇑(monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
        (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))) (-w) =
      (-1 : ℂ) ^ p *
        𝓕 (⇑(monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))) w := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have h := integral_neg_eq_self
    (fun v : ℝ =>
      Complex.exp (↑(-2 * Real.pi * v * -w) * Complex.I) •
        monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) v) volume
  rw [← h, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [monomialRvachevSchwartz_apply, monomialRvachevSchwartz_apply]
  have hup : rvachevUp F (((M : ℝ))⁻¹ * -v) =
      rvachevUp F (((M : ℝ))⁻¹ * v) := by
    rw [mul_neg]
    exact rvachevUp_even F _
  have harg : (-2 * Real.pi * -v * -w : ℝ) = -2 * Real.pi * v * w := by
    ring
  rw [hup, harg, smul_eq_mul, smul_eq_mul, neg_pow_ofReal_mul]
  ring

/-- Parity at integer frequencies. -/
theorem fourier_monomialRvachevSchwartz_int_neg (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) (p : ℕ) (ℓ : ℤ) :
    𝓕 (⇑(monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
        (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))) (((-ℓ : ℤ) : ℝ)) =
      (-1 : ℂ) ^ p *
        𝓕 (⇑(monomialRvachevSchwartz F hF p ((M : ℝ))⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr hM)))) ((ℓ : ℤ) : ℝ) := by
  have h := fourier_monomialRvachevSchwartz_neg F hF hM p (ℓ : ℝ)
  simpa using h

/-- **Endpoint super-exactness at odd threshold degree**: when
`v₂(M)+1` is odd — every odd mesh, and every mesh of even two-adic
valuation — the endpoint comb is exact one degree beyond the shifted
threshold: the surviving odd-frequency aliases cancel in `±` pairs by
coefficient parity. -/
theorem tsum_monomial_eq_integral_of_odd_deg (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    (hodd : Odd (padicValNat 2 M + 1)) :
    (∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (k : ℝ)) =
      ∫ x : ℝ, ((x ^ (padicValNat 2 M + 1) *
        rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) := by
  have h := tsum_shifted_monomial_sub_integral_odd F hF hM 0
  have hcomb : (∑' k : ℤ, monomialRvachevSchwartz F hF
      (padicValNat 2 M + 1) ((M : ℝ))⁻¹
      (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) ((0 : ℝ) + k)) =
      ∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (k : ℝ) :=
    tsum_congr fun k => by rw [zero_add]
  rw [hcomb] at h
  have h0c : ((0 : ℝ) : UnitAddCircle) = 0 := by norm_num
  have hT : (∑' ℓ : ℤ, if Odd ℓ then
      𝓕 (monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
          ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ *
        fourier ℓ (((0 : ℝ)) : UnitAddCircle) else 0) = 0 := by
    set f : ℤ → ℂ := fun ℓ => if Odd ℓ then
      𝓕 (monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
          ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ *
        fourier ℓ (((0 : ℝ)) : UnitAddCircle) else 0 with hf
    have hneg : ∀ ℓ : ℤ, f (-ℓ) = -f ℓ := by
      intro ℓ
      simp only [hf]
      by_cases hℓ : Odd ℓ
      · rw [if_pos (odd_neg.mpr hℓ), if_pos hℓ, h0c,
          fourier_eval_zero, fourier_eval_zero, mul_one, mul_one]
        show 𝓕 (⇑(monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
            ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))))
            (((-ℓ : ℤ)) : ℝ) =
          -(𝓕 (⇑(monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
            ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))))
            ((ℓ : ℤ) : ℝ))
        have hpar := fourier_monomialRvachevSchwartz_int_neg F hF hM
          (padicValNat 2 M + 1) ℓ
        rw [Odd.neg_one_pow hodd, neg_one_mul] at hpar
        exact hpar
      · rw [if_neg (fun hc => hℓ (odd_neg.mp hc)), if_neg hℓ,
          neg_zero]
    have hswap : ∑' ℓ : ℤ, f (-ℓ) = ∑' ℓ : ℤ, f ℓ :=
      (Equiv.neg ℤ).tsum_eq f
    have hminus : ∑' ℓ : ℤ, f (-ℓ) = -∑' ℓ : ℤ, f ℓ := by
      calc ∑' ℓ : ℤ, f (-ℓ) = ∑' ℓ : ℤ, -(f ℓ) := tsum_congr hneg
        _ = -∑' ℓ : ℤ, f ℓ := tsum_neg
    have hTT : ∑' ℓ : ℤ, f ℓ = -∑' ℓ : ℤ, f ℓ :=
      hswap.symm.trans hminus
    exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hTT)
  rw [hT] at h
  exact sub_eq_zero.mp h

/-- **The endpoint Dirichlet fold at even threshold degree**: when
`v₂(M)+1` is even, the `±ℓ` aliases reinforce and the endpoint defect
is twice the one-sided odd-frequency series — the comb volume's
`D`-series form on the up-side. -/
theorem tsum_shifted_monomial_sub_integral_even_deg
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    (heven : Even (padicValNat 2 M + 1)) :
    (∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (k : ℝ)) -
      ∫ x : ℝ, ((x ^ (padicValNat 2 M + 1) *
        rvachevUp F (((M : ℝ))⁻¹ * x) : ℝ) : ℂ) =
      2 * ∑' n : ℕ, (if Odd n then
        𝓕 (⇑(monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
            ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))))
          ((n : ℕ) : ℝ) else 0) := by
  have h := tsum_shifted_monomial_sub_integral_odd F hF hM 0
  have hcomb : (∑' k : ℤ, monomialRvachevSchwartz F hF
      (padicValNat 2 M + 1) ((M : ℝ))⁻¹
      (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) ((0 : ℝ) + k)) =
      ∑' k : ℤ, monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM)) (k : ℝ) :=
    tsum_congr fun k => by rw [zero_add]
  rw [hcomb] at h
  rw [h]
  set f : ℤ → ℂ := fun ℓ => if Odd ℓ then
    𝓕 (monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
        ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))) ℓ *
      fourier ℓ (((0 : ℝ)) : UnitAddCircle) else 0 with hf
  have hsum : Summable f := by
    have hbig := summable_fourier_monomialRvachevSchwartz F hF hM
      (padicValNat 2 M + 1) 0
    refine (hbig.indicator {ℓ : ℤ | Odd ℓ}).congr fun ℓ => ?_
    rw [Set.indicator_apply]
    by_cases hℓ : Odd ℓ <;> simp [hℓ, hf]
  have hnegf : ∀ ℓ : ℤ, f (-ℓ) = f ℓ := by
    intro ℓ
    simp only [hf]
    by_cases hℓ : Odd ℓ
    · rw [if_pos (odd_neg.mpr hℓ), if_pos hℓ]
      have h0c : ((0 : ℝ) : UnitAddCircle) = 0 := by norm_num
      rw [h0c, fourier_eval_zero, fourier_eval_zero, mul_one, mul_one]
      show 𝓕 (⇑(monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
          ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))))
          (((-ℓ : ℤ)) : ℝ) =
        𝓕 (⇑(monomialRvachevSchwartz F hF (padicValNat 2 M + 1)
          ((M : ℝ))⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr hM))))
          ((ℓ : ℤ) : ℝ)
      have hpar := fourier_monomialRvachevSchwartz_int_neg F hF hM
        (padicValNat 2 M + 1) ℓ
      rw [Even.neg_one_pow heven, one_mul] at hpar
      exact hpar
    · rw [if_neg (fun hc => hℓ (odd_neg.mp hc)), if_neg hℓ]
  have hf0 : f 0 = 0 := by
    simp [hf, Int.odd_iff]
  have hfnat : Summable (fun n : ℕ => f (n : ℤ)) :=
    hsum.comp_injective Nat.cast_injective
  have hfnat1 : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    hsum.comp_injective fun a b hab => by omega
  have hfold := tsum_nat_add_neg_add_one hsum
  have hstep : ∀ n : ℕ,
      f (n : ℤ) + f (-((n : ℤ) + 1)) = f (n : ℤ) + f ((n : ℤ) + 1) :=
    fun n => by rw [hnegf ((n : ℤ) + 1)]
  have hshift : ∑' n : ℕ, f ((n : ℤ) + 1) = ∑' n : ℕ, f (n : ℤ) := by
    have hzero := (tsum_eq_zero_add hfnat)
    have hcast : ∀ n : ℕ, f (((n + 1 : ℕ)) : ℤ) = f ((n : ℤ) + 1) :=
      fun n => by push_cast; rfl
    calc ∑' n : ℕ, f ((n : ℤ) + 1)
        = ∑' n : ℕ, f (((n + 1 : ℕ)) : ℤ) :=
          tsum_congr fun n => (hcast n).symm
      _ = ∑' n : ℕ, f (n : ℤ) := by
          rw [hzero, hf0, zero_add]
  have hZ : ∑' ℓ : ℤ, f ℓ = 2 * ∑' n : ℕ, f (n : ℤ) := by
    calc ∑' ℓ : ℤ, f ℓ
        = ∑' n : ℕ, (f (n : ℤ) + f (-((n : ℤ) + 1))) := hfold.symm
      _ = ∑' n : ℕ, (f (n : ℤ) + f ((n : ℤ) + 1)) :=
          tsum_congr hstep
      _ = (∑' n : ℕ, f (n : ℤ)) + ∑' n : ℕ, f ((n : ℤ) + 1) :=
          hfnat.tsum_add hfnat1
      _ = 2 * ∑' n : ℕ, f (n : ℤ) := by
          rw [hshift]
          ring
  rw [hZ]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [hf]
  by_cases hn : Odd n
  · rw [if_pos ((Int.odd_coe_nat n).mpr hn), if_pos hn]
    have h0c : ((0 : ℝ) : UnitAddCircle) = 0 := by norm_num
    rw [h0c, fourier_eval_zero, mul_one]
    rfl
  · rw [if_neg (fun hc => hn ((Int.odd_coe_nat n).mp hc)), if_neg hn]

end Fabius
