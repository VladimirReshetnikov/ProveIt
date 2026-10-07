import OAI.Combinatorics.Progressions.Fourier.CanonicalDensityFourier

namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

noncomputable def maskedIntegerPeriodization (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) : ℝ :=
  ∑' n : D → ℤ, mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ))

omit [Fintype D] in
private theorem masked_shift_nonzero (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) (n : D → ℤ)
    (h : mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ)) ≠ 0) :
    H (fun i => x i + (n i : ℝ)) ≠ 0 := (mul_ne_zero_iff.mp h).2

theorem maskedIntegerPeriodization_lipschitz (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {L : ℝ≥0} (hH : LipschitzWith L H)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith L (maskedIntegerPeriodization q mask H) := by
  apply separated_tsum_lipschitz
  · intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hH.dist_le_mul (x + fun i => (n i : ℝ)) (y + fun i => (n i : ℝ))
    rw [dist_add_right] at h
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (hmask _).1]
    calc
      _ ≤ 1 * |H (fun i => x i + (n i : ℝ)) - H (fun i => y i + (n i : ℝ))| :=
        mul_le_mul_of_nonneg_right (hmask _).2 (abs_nonneg _)
      _ ≤ L * dist x y := by simpa only [one_mul, Real.dist_eq, Pi.add_def] using h
  · intro n x
    exact mul_nonneg (hmask _).1 (h0 _)
  · intro x n k hn hk
    exact integer_shifts_small_box_injective x n k
      (hs _ (masked_shift_nonzero q mask H x n hn))
      (hs _ (masked_shift_nonzero q mask H x k hk))

omit [Fintype D] in
theorem maskedIntegerPeriodization_local (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (x : D → ℝ) (hx : ∀ i, |x i| < 1/2) (k : D → ℤ) :
    maskedIntegerPeriodization q mask H (fun i => x i + (k i : ℝ)) =
      mask (fun i => (-k i : ZMod q)) * H x := by
  unfold maskedIntegerPeriodization
  rw [tsum_eq_single (-k)]
  · simp
  · intro n hn
    by_contra hnonzero
    have hH := masked_shift_nonzero q mask H (fun i => x i + (k i : ℝ)) n hnonzero
    have he := integer_shifts_small_box_injective (fun i => x i + (k i : ℝ)) n (-k)
      (hs _ hH) (by simpa using hx)
    exact hn he

omit [Fintype D] in
theorem maskedIntegerPeriodization_range (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ) :
    maskedIntegerPeriodization q mask H x ∈ Set.Icc (0 : ℝ) B := by
  refine ⟨tsum_nonneg (fun n => mul_nonneg (hmask _).1 (hH _).1), ?_⟩
  by_cases hx : ∃ n : D → ℤ, H (fun i => x i + (n i : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hx
    unfold maskedIntegerPeriodization
    rw [tsum_eq_single n]
    · exact (mul_le_of_le_one_left (hH _).1 (hmask _).2).trans (hH _).2
    · intro k hk
      have hz : H (fun i => x i + (k i : ℝ)) = 0 := by
        by_contra hh
        exact hk (integer_shifts_small_box_injective x k n (hs _ hh) (hs _ hn))
      rw [hz, mul_zero]
  · have hz : ∀ n : D → ℤ, H (fun i => x i + (n i : ℝ)) = 0 := by simpa using hx
    simpa only [maskedIntegerPeriodization, hz, mul_zero, tsum_zero] using hB

omit [Fintype D] in
theorem maskedIntegerPeriodization_periodic (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) (k : D → ℤ) :
    maskedIntegerPeriodization q mask H (fun i => x i + q * (k i : ℝ)) =
      maskedIntegerPeriodization q mask H x := by
  unfold maskedIntegerPeriodization
  let v : D → ℤ := fun i => q * k i
  have h := (Equiv.addRight v).tsum_eq (fun n : D → ℤ =>
    mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ)))
  convert h using 1
  apply tsum_congr
  intro n
  congr 1
  · congr 1
    funext i
    simp [v]
  · congr 1
    funext i
    simp [v]
    ring

noncomputable def maskedIntegerTorusKernel (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) : (D → UnitAddCircle) → ℝ :=
  realPeriodicTorusLift (fun x => maskedIntegerPeriodization q mask H (fun i => q * x i))

omit [Fintype D] in
private theorem maskedIntegerPeriodization_rescale_periodic (q : ℕ)
    (mask : (D → ZMod q) → ℝ) (H : (D → ℝ) → ℝ)
    (x : D → ℝ) (k : D → ℤ) :
    maskedIntegerPeriodization q mask H (fun i => q * (x i + (k i : ℝ))) =
      maskedIntegerPeriodization q mask H (fun i => q * x i) := by
  simp_rw [mul_add]
  exact maskedIntegerPeriodization_periodic q mask H _ k

omit [Fintype D] in
theorem maskedIntegerTorusKernel_coe (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) :
    maskedIntegerTorusKernel q mask H (fun i => (x i : UnitAddCircle)) =
      maskedIntegerPeriodization q mask H (fun i => q * x i) :=
  realPeriodicTorusLift_coe _ (maskedIntegerPeriodization_rescale_periodic q mask H) x

theorem maskedIntegerTorusKernel_lipschitz (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {L : ℝ≥0} (hH : LipschitzWith L H)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith ((q : ℝ≥0) * L) (maskedIntegerTorusKernel q mask H) := by
  apply realPeriodicTorusLift_lipschitz _ _ (maskedIntegerPeriodization_rescale_periodic q mask H)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (maskedIntegerPeriodization_lipschitz q mask hmask H hH h0 hs).dist_le_mul
    ((q : ℝ) • x) ((q : ℝ) • y)
  rw [dist_smul₀] at h
  simpa only [Pi.smul_def, smul_eq_mul, Real.norm_natCast, NNReal.coe_mul,
    NNReal.coe_natCast, mul_assoc, mul_left_comm] using h

omit [Fintype D] in
theorem maskedIntegerTorusKernel_range (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → UnitAddCircle) :
    maskedIntegerTorusKernel q mask H x ∈ Set.Icc (0 : ℝ) B :=
  realPeriodicTorusLift_range _ (fun y =>
    maskedIntegerPeriodization_range q mask hmask H hB hH hs (fun i => q * y i)) x

omit [Fintype D] in
theorem maskedIntegerPeriodization_le (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ≤ 1) (H : (D → ℝ) → ℝ)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (x : D → ℝ) :
    maskedIntegerPeriodization q mask H x ≤ positiveIntegerPeriodization H x := by
  by_cases hx : ∃ n : D → ℤ, H (fun i => x i + (n i : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hx
    have hz (k : D → ℤ) (hk : k ≠ n) : H (fun i => x i + (k i : ℝ)) = 0 := by
      by_contra hh
      exact hk (integer_shifts_small_box_injective x k n (hs _ hh) (hs _ hn))
    unfold maskedIntegerPeriodization positiveIntegerPeriodization
    rw [tsum_eq_single n (fun k hk => by rw [hz k hk, mul_zero]), tsum_eq_single n hz]
    exact mul_le_of_le_one_left (h0 _) (hmask _)
  · have hz : ∀ n : D → ℤ, H (fun i => x i + (n i : ℝ)) = 0 := by simpa using hx
    simp only [maskedIntegerPeriodization, positiveIntegerPeriodization, hz, mul_zero, tsum_zero, le_refl]

omit [Fintype D] in
theorem maskedIntegerTorusKernel_one (q : ℕ) (H : (D → ℝ) → ℝ)
    (z : D → UnitAddCircle) :
    maskedIntegerTorusKernel q (fun _ => 1) H z = smallBoxTorusKernel H (q • z) := by
  let x : D → ℝ := fun i => centeredCircleLift (z i)
  have hx : (fun i => (x i : UnitAddCircle)) = z := funext (fun i => coe_centeredCircleLift _)
  have hqx : (fun i => (((q : ℝ) * x i : ℝ) : UnitAddCircle)) = q • z := by
    funext i
    simp only [← nsmul_eq_mul, AddCircle.coe_nsmul, x, coe_centeredCircleLift, Pi.smul_apply]
  rw [← hx, maskedIntegerTorusKernel_coe, hx, ← hqx]
  rw [smallBoxTorusKernel, realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  simp only [maskedIntegerPeriodization, positiveIntegerPeriodization, one_mul]

omit [Fintype D] in
theorem maskedIntegerTorusKernel_le (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ≤ 1) (H : (D → ℝ) → ℝ)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (z : D → UnitAddCircle) :
    maskedIntegerTorusKernel q mask H z ≤ smallBoxTorusKernel H (q • z) := by
  let x : D → ℝ := fun i => centeredCircleLift (z i)
  have hx : (fun i => (x i : UnitAddCircle)) = z := funext (fun i => coe_centeredCircleLift _)
  have hqx : (fun i => (((q : ℝ) * x i : ℝ) : UnitAddCircle)) = q • z := by
    funext i
    simp only [← nsmul_eq_mul, AddCircle.coe_nsmul, x, coe_centeredCircleLift, Pi.smul_apply]
  rw [← hx, maskedIntegerTorusKernel_coe, hx, ← hqx]
  rw [smallBoxTorusKernel, realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  exact maskedIntegerPeriodization_le q mask hmask H h0 hs _

omit [Fintype D] in
theorem maskedIntegerTorusKernel_local (q : ℕ) (hq : 0 < q)
    (mask : (D → ZMod q) → ℝ) (H : (D → ℝ) → ℝ)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (x : D → ℝ) (hx : ∀ i, |x i| < 1/2) (k : D → ℤ) :
    maskedIntegerTorusKernel q mask H
      (fun i => (((x i + (k i : ℝ)) / q : ℝ) : UnitAddCircle)) =
      mask (fun i => (-k i : ZMod q)) * H x := by
  rw [maskedIntegerTorusKernel_coe]
  have he : (fun i => (q : ℝ) * ((x i + (k i : ℝ)) / q)) =
      (fun i => x i + (k i : ℝ)) := by
    funext i
    field_simp
  rw [he]
  exact maskedIntegerPeriodization_local q mask H hs x hx k

theorem exists_masked_integer_fourier_approximation
    (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) (L B : ℝ≥0) (hH : LipschitzWith L H)
    (hB : ∀ x, H x ∈ Set.Icc (0 : ℝ) B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hD : (Fintype.card D : ℝ) ≤ P)
    (hLP : (q : ℝ) * L ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → D → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a i, |(frequency a i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * B ∧
      ∀ x : D → UnitAddCircle,
        ‖(maskedIntegerTorusKernel q mask H x : ℂ) -
          ∑ a, c a * ∏ i, CircleFourier.character (frequency a i • x i)‖ ≤ δ := by
  have hl : LipschitzWith ((q : ℝ≥0) * L)
      (fun x => (maskedIntegerTorusKernel q mask H x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact (maskedIntegerTorusKernel_lipschitz q mask hmask H hH (fun x => (hB x).1) hs).dist_le_mul x y
  have hb (x : D → UnitAddCircle) : ‖(maskedIntegerTorusKernel q mask H x : ℂ)‖ ≤ B := by
    obtain ⟨h0, hcap⟩ := maskedIntegerTorusKernel_range q mask hmask H B.coe_nonneg hB hs x
    simpa only [Complex.norm_real, Real.norm_of_nonneg h0] using hcap
  exact exists_ambient_torus_fourier_approximation _ _ B hl hb hδ hP hD
    (by simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hLP) hδP

end Erdos3

end

end OAI
