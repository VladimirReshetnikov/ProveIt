import FabiusFunction.PerronRootExistence

/-!
# Uniqueness of the Perron eigenvalue

The RPF rigidity available already at the order-theoretic level:
**any** continuous eigenfunction of the transfer operator that is
strictly positive on `[0,1]` has its eigenvalue equal to the Fekete
growth rate of `𝓛ⁿ𝟙`.  With `m ≤ h ≤ M` on `[0,1]`, `0 < m ≤ M`,

`ρⁿ·(m/M) ≤ 𝓛ⁿ𝟙 ≤ ρⁿ·(M/m)`  on `[0,1]`,

so `aₙ^{1/n} → ρ`; by uniqueness of limits any two positive continuous
eigenfunctions share their eigenvalue — the audits' `ρ₁` is pinned as
soon as an eigenfunction is produced.

* `iterate_eigen` — `𝓛ⁿh = ρⁿ·h` on `[0,1]`.
* `tendsto_transferSup_rpow_of_eigenfunction` — the sandwich limit.
* `perron_eigenvalue_unique` — two positive eigenvalues coincide.
-/

set_option autoImplicit false

open Real Set Filter Topology

namespace Fabius

/-- The eigenrelation iterates: `𝓛ⁿh = ρⁿ·h` on `[0,1]`. -/
theorem iterate_eigen {h : ℝ → ℝ} {ρ : ℝ}
    (heig : ∀ x ∈ Set.Icc (0:ℝ) 1, rpfTransfer h x = ρ * h x) (n : ℕ) :
    ∀ x ∈ Set.Icc (0:ℝ) 1,
      (rpfTransfer^[n] h) x = ρ ^ n * h x := by
  induction n with
  | zero =>
      intro x _
      simp
  | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply', rpfTransfer_apply]
      have hL := ih _ (branch_left_mem hx)
      have hR := ih _ (branch_right_mem hx)
      rw [hL, hR]
      have hstep := heig x hx
      rw [rpfTransfer_apply] at hstep
      calc (Real.sin (π * x / 2) * (ρ ^ n * h (x / 2)) +
          Real.cos (π * x / 2) * (ρ ^ n * h ((x + 1) / 2))) / 2 =
          ρ ^ n * ((Real.sin (π * x / 2) * h (x / 2) +
            Real.cos (π * x / 2) * h ((x + 1) / 2)) / 2) := by ring
        _ = ρ ^ n * (ρ * h x) := by rw [hstep]
        _ = ρ ^ (n + 1) * h x := by ring

/-- Auxiliary limit: `(ρⁿ·c)^{1/n} → ρ` for positive `ρ, c`. -/
theorem tendsto_pow_mul_const_rpow {ρ c : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) :
    Tendsto (fun n : ℕ => (ρ ^ n * c) ^ ((1:ℝ) / n))
      atTop (𝓝 ρ) := by
  have hdiv : Tendsto (fun n : ℕ => Real.log c / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hexp : Tendsto (fun n : ℕ => Real.exp (Real.log c / n))
      atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hdiv
    rwa [Real.exp_zero] at h
  have hmul : Tendsto (fun n : ℕ => ρ * Real.exp (Real.log c / n))
      atTop (𝓝 ρ) := by
    have h := hexp.const_mul ρ
    rwa [mul_one] at h
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : ((n:ℝ)) ≠ 0 := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hpos : 0 < ρ ^ n * c := by positivity
  rw [Real.rpow_def_of_pos hpos, Real.log_mul (by positivity) hc.ne',
    Real.log_pow]
  rw [show (↑n * Real.log ρ + Real.log c) * (1 / ↑n) =
      Real.log ρ + Real.log c / ↑n by field_simp,
    Real.exp_add, Real.exp_log hρ]

/-- **The sandwich**: a positive continuous eigenfunction forces
`aₙ^{1/n} → ρ`. -/
theorem tendsto_transferSup_rpow_of_eigenfunction {h : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hcont : Continuous h)
    (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < h x)
    (heig : ∀ x ∈ Set.Icc (0:ℝ) 1, rpfTransfer h x = ρ * h x) :
    Tendsto (fun n : ℕ => (transferSup n) ^ ((1:ℝ) / n))
      atTop (𝓝 ρ) := by
  obtain ⟨xm, hxm, hminOn⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr zero_le_one) hcont.continuousOn
  obtain ⟨xM, hxM, hmaxOn⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) hcont.continuousOn
  set m : ℝ := h xm with hm
  set M : ℝ := h xM with hM
  have hm0 : 0 < m := hpos _ hxm
  have hM0 : 0 < M := hpos _ hxM
  have hmle : ∀ x ∈ Set.Icc (0:ℝ) 1, m ≤ h x := fun x hx => hminOn hx
  have hMge : ∀ x ∈ Set.Icc (0:ℝ) 1, h x ≤ M := fun x hx => hmaxOn hx
  -- pointwise upper: 𝓛ⁿ𝟙 ≤ ρⁿ·(M/m) on [0,1]
  have hup : ∀ n : ℕ, transferSup n ≤ ρ ^ n * (M / m) := by
    intro n
    apply csSup_le (transferSup_image_nonempty n)
    rintro y ⟨x, hx, rfl⟩
    have hone : ∀ z ∈ Set.Icc (0:ℝ) 1,
        (fun _ : ℝ => (1:ℝ)) z ≤ (fun y => m⁻¹ * h y) z := by
      intro z hz
      show (1:ℝ) ≤ m⁻¹ * h z
      calc (1:ℝ) = m⁻¹ * m := by
            rw [inv_mul_cancel₀ hm0.ne']
        _ ≤ m⁻¹ * h z :=
            mul_le_mul_of_nonneg_left (hmle z hz) (by positivity)
    have h1 := iterate_rpfTransfer_mono n hone x hx
    have h2 := iterate_rpfTransfer_const_mul m⁻¹ h n
    have h3 := iterate_eigen heig n x hx
    calc (rpfTransfer^[n] (fun _ => 1)) x ≤
        (rpfTransfer^[n] (fun y => m⁻¹ * h y)) x := h1
      _ = m⁻¹ * (rpfTransfer^[n] h) x := by rw [h2]
      _ = m⁻¹ * (ρ ^ n * h x) := by rw [h3]
      _ ≤ m⁻¹ * (ρ ^ n * M) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hMge x hx) (by positivity)
      _ = ρ ^ n * (M / m) := by field_simp
  -- pointwise lower: ρⁿ·(m/M) ≤ aₙ
  have hlow : ∀ n : ℕ, ρ ^ n * (m / M) ≤ transferSup n := by
    intro n
    have hx0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
    have hMone : ∀ z ∈ Set.Icc (0:ℝ) 1,
        h z ≤ (fun y => M * (fun _ : ℝ => (1:ℝ)) y) z := by
      intro z hz
      show h z ≤ M * 1
      rw [mul_one]
      exact hMge z hz
    have h1 := iterate_rpfTransfer_mono n hMone 0 hx0
    have h2 := iterate_rpfTransfer_const_mul M (fun _ => (1:ℝ)) n
    have h3 := iterate_eigen heig n 0 hx0
    have h4 : ρ ^ n * h 0 ≤ M * (rpfTransfer^[n] (fun _ => 1)) 0 := by
      calc ρ ^ n * h 0 = (rpfTransfer^[n] h) 0 := (h3).symm
        _ ≤ (rpfTransfer^[n] (fun y => M * (fun _ : ℝ => (1:ℝ)) y)) 0 :=
            h1
        _ = M * (rpfTransfer^[n] (fun _ => 1)) 0 := by rw [h2]
    have h5 : ρ ^ n * (m / M) ≤ (rpfTransfer^[n] (fun _ => 1)) 0 := by
      have hm0' := hmle 0 hx0
      rw [show ρ ^ n * (m / M) = ρ ^ n * m / M by ring,
        div_le_iff₀ hM0]
      nlinarith [h4, pow_pos hρ n]
    exact le_trans h5 (apply_le_transferSup n hx0)
  -- squeeze
  have hlowlim := tendsto_pow_mul_const_rpow hρ
    (show (0:ℝ) < m / M by positivity)
  have huplim := tendsto_pow_mul_const_rpow hρ
    (show (0:ℝ) < M / m by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim huplim
  · filter_upwards with n
    apply Real.rpow_le_rpow (by positivity) (hlow n) (by positivity)
  · filter_upwards with n
    apply Real.rpow_le_rpow ?_ (hup n) (by positivity)
    exact le_trans (by positivity) (hlow n)

/-- **Uniqueness of the Perron eigenvalue**: two continuous
eigenfunctions positive on `[0,1]` have the same eigenvalue. -/
theorem perron_eigenvalue_unique {h₁ h₂ : ℝ → ℝ} {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hcont₁ : Continuous h₁) (hcont₂ : Continuous h₂)
    (hpos₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < h₁ x)
    (hpos₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < h₂ x)
    (heig₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, rpfTransfer h₁ x = ρ₁ * h₁ x)
    (heig₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, rpfTransfer h₂ x = ρ₂ * h₂ x) :
    ρ₁ = ρ₂ :=
  tendsto_nhds_unique
    (tendsto_transferSup_rpow_of_eigenfunction hρ₁ hcont₁ hpos₁ heig₁)
    (tendsto_transferSup_rpow_of_eigenfunction hρ₂ hcont₂ hpos₂ heig₂)

end Fabius
