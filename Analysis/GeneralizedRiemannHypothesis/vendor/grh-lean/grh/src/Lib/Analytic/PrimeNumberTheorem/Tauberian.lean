import Lib.Analytic.EntireLFunction

/-!
# A Tauberian theorem with a power of the logarithm

Let `R` be measurable and Lipschitz on `v ≥ 0`, and let its transform `∫₀^∞ R(v) e^{(1 - s) v} dv`
be `(F s - F 1) / (s - 1)` in `re s > 2`. Suppose that for all large `l` the function `F` is
holomorphic and at most `l ^ A` on `re s ≥ 1 - l ^ (-A)`, `|s| ≤ e ^ l`. Then `R(v) = O(v ^ (-B))`
for every `B`. The theorem is meant for the remainder in the prime number theorem for a sum over
prime powers with weights that vanish at the cutoff `x`: at `x = e ^ v` it is Lipschitz in `v`.

The proof reads one Taylor coefficient of the transform at a far point `1 + H` in two ways. It is a
mean of `R` against a Gamma density that is concentrated at the given point `u`, hence close to
`R(u)`; and it is small by Cauchy's estimate on a disc that reaches left of the line `re s = 1`.

## Relation to the literature

Known result: the passage from a zero-free region to the error term of the prime number theorem.
Source: Montgomery and Vaughan, Multiplicative Number Theory I, 2007, Section 6.2, where a contour
integral is used in place of the Taylor coefficient.
-/

open Complex Filter MeasureTheory Metric Set Topology

open scoped Nat Real

namespace New

/-- Differentiation under the integral sign. Let `R` be measurable with `|R v| ≤ C e^v` for
`v ≥ 0`, and let `Φ s` be its transform `∫₀^∞ R(v) e^{(1 - s) v} dv` in `re s > 2`. Then, for such
`s`, the function `(-v)^k R(v) e^{(1 - s) v}` is integrable on `(0, ∞)`, and its integral is the
`k`-th derivative of `Φ` at `s`. -/
lemma iteratedDeriv_transform {R : ℝ → ℝ} {C : ℝ} {Φ : ℂ → ℂ} (hR : Measurable R)
    (R_le : ∀ v : ℝ, 0 ≤ v → |R v| ≤ C * rexp v)
    (Φ_eq : ∀ s : ℂ, 2 < s.re → Φ s = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v)) (k : ℕ) (s : ℂ)
    (hs : 2 < s.re) :
    IntegrableOn (fun v : ℝ ↦ (-v) ^ k * R v * cexp ((1 - s) * v)) (Ioi 0) ∧
      iteratedDeriv k Φ s = ∫ v in Ioi (0 : ℝ), (-v) ^ k * R v * cexp ((1 - s) * v) := by
  induction k generalizing s with
  | zero => simp [integrableOn_laplace_of_abs_le hR R_le hs, Φ_eq s hs]
  | succ k ih =>
    obtain ⟨ε, hε, hεs⟩ : ∃ ε > 0, 2 * ε < s.re - 2 := exists_pos_mul_lt (sub_pos.2 hs) 2
    have h_nhds : {z : ℂ | 2 < z.re} ∈ 𝓝 s := (isOpen_re_gt _).mem_nhds hs
    let G (z : ℂ) (v : ℝ) : ℂ := (-v) ^ k * R v * cexp ((1 - z) * v)
    -- On `re z > 2 ε + 2` the derivative in `z` is dominated by `‖G (ε + 2)‖ / ε`, since
    -- `ε v ≤ e^{ε v}`.
    have h_dom (v : ℝ) (hv : 0 < v) (z : ℂ) (hz : 2 * ε + 2 < z.re) :
        ‖-v * G z v‖ ≤ ‖G (ε + 2) v‖ / ε := by
      have h_exp_le : v * ε * rexp ((1 - z.re) * v) ≤ rexp ((1 - (ε + 2)) * v) := by
        grw [lt_add_one (v * ε), Real.add_one_le_exp, ← Real.exp_add, Real.exp_le_exp]
        nlinarith
      have h_norm (w : ℂ) : ‖G w v‖ = v ^ k * |R v| * rexp ((1 - w.re) * v) := by
        simp [G, abs_of_pos hv, norm_exp]
      rw [norm_mul, norm_neg, norm_real, Real.norm_of_nonneg hv.le, h_norm, h_norm, add_re,
        ofReal_re, re_ofNat, le_div_iff₀ hε]
      calc v * (v ^ k * |R v| * rexp ((1 - z.re) * v)) * ε
          = v ^ k * |R v| * (v * ε * rexp ((1 - z.re) * v)) := by ring
        _ ≤ v ^ k * |R v| * rexp ((1 - (ε + 2)) * v) := by gcongr
    have h_diff (v : ℝ) (z : ℂ) : HasDerivAt (fun z : ℂ ↦ G z v) (-v * G z v) z := by
      simpa [G, mul_comm, mul_left_comm] using
        (((hasDerivAt_id z).const_sub 1).mul_const (v : ℂ)).cexp.const_mul ((-v : ℂ) ^ k * R v)
    have h_meas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (G z) (volume.restrict (Ioi 0)) :=
      .mono h_nhds fun z hz ↦ (ih z hz).left.aestronglyMeasurable
    have h_bound_int : IntegrableOn (fun v : ℝ ↦ ‖G (ε + 2) v‖ / ε) (Ioi 0) :=
      (ih (ε + 2) (by simpa)).left.norm.div_const ε
    obtain ⟨h_int, h_deriv⟩ : IntegrableOn (fun v : ℝ ↦ -v * G s v) (Ioi 0) volume ∧
        HasDerivAt (fun z : ℂ ↦ ∫ v in Ioi 0, G z v) (∫ v in Ioi 0, -v * G s v) s :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        ((isOpen_re_gt _).mem_nhds (lt_tsub_iff_right.1 hεs)) h_meas (ih s hs).left (by fun_prop)
        (ae_restrict_of_forall_mem measurableSet_Ioi h_dom) h_bound_int
        (.of_forall fun v z _ ↦ h_diff v z)
    have h_eq : iteratedDeriv k Φ =ᶠ[𝓝 s] fun z : ℂ ↦ ∫ v in Ioi 0, G z v :=
      .mono h_nhds fun z hz ↦ (ih z hz).right
    have h_succ (v : ℝ) : (-v : ℂ) ^ (k + 1) * R v * cexp ((1 - s) * v) = -v * G s v := by
      simp [G, pow_succ', mul_assoc]
    simp only [h_succ, iteratedDeriv_succ]
    exact ⟨h_int, (h_deriv.congr_of_eventuallyEq h_eq).deriv⟩

/-- For `H > 0` the moments of `e^{-H v}` on `(0, ∞)` exist: the function `v ^ j e^{-H v}` is
integrable there, with integral `j! / H ^ (j + 1)`. -/
lemma integrableOn_and_integral_pow_mul_exp_neg_mul {H : ℝ} (hH : 0 < H) (j : ℕ) :
    IntegrableOn (fun v : ℝ ↦ v ^ j * rexp (-H * v)) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), v ^ j * rexp (-H * v) = j ! / H ^ (j + 1) := by
  have h_eq : ∫ v in Ioi (0 : ℝ), v ^ j * rexp (-H * v) = j ! / H ^ (j + 1) :=
    mod_cast laplace_pow (s := H) (by simpa) j
  exact ⟨.of_integral_ne_zero (h_eq.trans_ne (by positivity)), h_eq⟩

/-- For `H > 0` and the mean `u = (k + 1) / H` of the Gamma density
`H ^ (k + 1) v ^ k e^{-H v} / k!`, the function `v ^ k e^{-H v} (a + b (v - u)²)` is integrable on
`(0, ∞)`, with integral `k! / H ^ (k + 1) (a + b (k + 1) / H²)`. -/
lemma integrableOn_and_integral_gamma_mul_quadratic {H : ℝ} (hH : 0 < H) (k : ℕ) (a b : ℝ) :
    IntegrableOn (fun v : ℝ ↦ v ^ k * rexp (-H * v) * (a + b * (v - (k + 1) / H) ^ 2)) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (a + b * (v - (k + 1) / H) ^ 2) =
        k ! / H ^ (k + 1) * (a + b * ((k + 1) / H ^ 2)) := by
  let f (j : ℕ) (v : ℝ) : ℝ := v ^ j * rexp (-H * v)
  have h_moment (j : ℕ) : IntegrableOn (f j) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), f j v = j ! / H ^ (j + 1) :=
    integrableOn_and_integral_pow_mul_exp_neg_mul hH j
  have h_expand (v : ℝ) : v ^ k * rexp (-H * v) * (a + b * (v - (k + 1) / H) ^ 2) =
      (a + b * ((k + 1) / H) ^ 2) * f k v - 2 * b * ((k + 1) / H) * f (k + 1) v +
        b * f (k + 2) v := by ring
  have h_int (j : ℕ) (c : ℝ) : IntegrableOn (fun v : ℝ ↦ c * f j v) (Ioi 0) :=
    (h_moment j).left.const_mul c
  simp only [h_expand]
  refine ⟨((h_int k _).sub (h_int (k + 1) _)).add (h_int (k + 2) _), ?_⟩
  rw [integral_add ((h_int k _).sub' (h_int (k + 1) _)) (h_int (k + 2) _),
    integral_sub (h_int k _) (h_int (k + 1) _)]
  simp only [integral_const_mul, (h_moment _).right, Nat.factorial_succ]
  push_cast
  field

variable {R : ℝ → ℝ} {F Φ : ℂ → ℂ} {C L : ℝ}

/-- Let `R` be measurable with `|R v| ≤ C e^v` for `v ≥ 0`, let `Φ s` be its transform
`∫₀^∞ R(v) e^{(1 - s) v} dv` in `re s > 2`, and let `H > 1`. The number
`(-H) ^ k H Φ⁽ᵏ⁾(1 + H) / k!` is the mean of `R` for the Gamma density
`H ^ (k + 1) v ^ k e^{-H v} / k!`, which has mean `(k + 1) / H` and variance `(k + 1) / H²`. So if
`|R v - c| ≤ a + b (v - (k + 1) / H)²` for all `v > 0`, it is within `a + b (k + 1) / H²` of `c`. -/
lemma norm_taylorCoeff_transform_sub_le (hR : Measurable R)
    (R_le : ∀ v : ℝ, 0 ≤ v → |R v| ≤ C * rexp v)
    (Φ_eq : ∀ s : ℂ, 2 < s.re → Φ s = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v))
    {H a b c : ℝ} (hH : 1 < H) (k : ℕ)
    (h_near : ∀ v : ℝ, 0 < v → |R v - c| ≤ a + b * (v - (k + 1) / H) ^ 2) :
    ‖(-H) ^ k * H / k ! * iteratedDeriv k Φ (1 + H) - c‖ ≤ a + b * ((k + 1) / H ^ 2) := by
  have hH_pos : 0 < H := one_pos.trans hH
  obtain ⟨moment_int, moment⟩ := integrableOn_and_integral_pow_mul_exp_neg_mul hH_pos k
  obtain ⟨int_major, major_integral⟩ :=
    integrableOn_and_integral_gamma_mul_quadratic hH_pos k a b
  have hH_re : 2 < (1 + H : ℂ).re := by simpa using (by linarith : 2 < 1 + H)
  obtain ⟨h_int, h_deriv⟩ := iteratedDeriv_transform hR R_le Φ_eq k (1 + H) hH_re
  have h_real (v : ℝ) : (-v) ^ k * R v * cexp ((1 - (1 + H)) * v) =
      (-1) ^ k * (v ^ k * rexp (-H * v) * R v : ℝ) := by
    push_cast
    ring_nf
  simp only [h_real] at h_int h_deriv
  rw [IntegrableOn, integrable_const_mul_iff (by simp)] at h_int
  -- The difference is the mean of `R - c`.
  have h_split : ∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (R v - c) =
      (∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * R v) - k ! / H ^ (k + 1) * c := by
    simp only [mul_sub]
    rw [integral_sub (mod_cast h_int.re) (moment_int.mul_const c), integral_mul_const, moment]
  have h_mean : (-H) ^ k * H / k ! * iteratedDeriv k Φ (1 + H) - c =
      (H ^ (k + 1) / k ! * ∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (R v - c) : ℝ) := by
    have h_pow : ((-H) ^ k * (-1) ^ k : ℂ) = H ^ k := by simp [← mul_pow]
    have h_sign (z : ℂ) : (-H) ^ k * H / k ! * ((-1) ^ k * z) = H ^ (k + 1) / k ! * z := by
      linear_combination (H / k ! * z) * h_pow
    have h_mass : H ^ (k + 1) / k ! * (k ! / H ^ (k + 1) * c) = c := by field
    rw [h_deriv, integral_const_mul, integral_complex_ofReal, h_sign, h_split, mul_sub, h_mass]
    norm_num
  rw [h_mean, norm_real, norm_mul, Real.norm_of_nonneg (by positivity)]
  calc H ^ (k + 1) / k ! * ‖∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (R v - c)‖
      ≤ H ^ (k + 1) / k ! *
        ∫ v in Ioi (0 : ℝ), v ^ k * rexp (-H * v) * (a + b * (v - (k + 1) / H) ^ 2) := by
        gcongr
        refine norm_integral_le_of_norm_le int_major
          (ae_restrict_of_forall_mem measurableSet_Ioi fun v (hv : 0 < v) ↦ ?_)
        grw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, h_near v hv]
    _ = a + b * ((k + 1) / H ^ 2) := by
        rw [major_integral]
        field

/-- Cauchy's estimate for the derivatives of the slope `(F s - F 1) / (s - 1)`, written
`dslope F 1`, at `1 + H`: if `F` is holomorphic and at most `M` in norm on the disc of radius
`H + η` about `1 + H`, the `k`-th one is at most `k! (2 M / η) / (H + η) ^ k`. Indeed
`|s - 1| ≥ η` on the boundary of the disc. -/
lemma norm_iteratedDeriv_dslope_le {H η M : ℝ} (hH : 0 ≤ H) (hη : 0 < η)
    (hF : ∀ s ∈ closedBall (1 + H : ℂ) (H + η), DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ M) (k : ℕ) :
    ‖iteratedDeriv k (dslope F 1) (1 + H)‖ ≤ k ! * (2 * M / η) / (H + η) ^ k := by
  have h_one : (1 : ℂ) ∈ ball (1 + H : ℂ) (H + η) := by
    simp [dist_eq_norm, abs_of_nonneg hH, hη]
  have h_nhds : closedBall (1 + H : ℂ) (H + η) ∈ 𝓝 1 :=
    mem_of_superset (isOpen_ball.mem_nhds h_one) ball_subset_closedBall
  have h_diff : DifferentiableOn ℂ (dslope F 1) (closedBall (1 + H) (H + η)) :=
    (differentiableOn_dslope h_nhds).2 fun s hs ↦ (hF s hs).left.differentiableWithinAt
  refine norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by positivity)
    (h_diff.diffContOnCl_ball le_rfl) fun s hs ↦ ?_
  have h_centre : dist (1 : ℂ) (1 + H) = H := by simp [dist_eq_norm, hH]
  have h_far : η ≤ ‖s - 1‖ := by
    linarith [dist_triangle s 1 (1 + H), mem_sphere.1 hs, dist_eq_norm s 1]
  rw [le_div_iff₀' hη]
  calc η * ‖dslope F 1 s‖ ≤ ‖(s - 1) • dslope F 1 s‖ := by grw [norm_smul, h_far]
    _ = ‖F s - F 1‖ := by rw [sub_smul_dslope]
    _ ≤ ‖F s‖ + ‖F 1‖ := norm_sub_le _ _
    _ ≤ 2 * M := by
        linarith [(hF s (sphere_subset_closedBall hs)).right,
          (hF 1 (ball_subset_closedBall h_one)).right]

/-- The normalised Taylor coefficient `(-H) ^ k H / k! · g⁽ᵏ⁾(1 + H)` of the slope `g = dslope F 1`,
that is `(F s - F 1) / (s - 1)`, is at most `4 M H / η · exp (-(k + 1) η / (2 H))` in norm if `F`
is holomorphic and at most `M` in norm on the disc about `1 + H` that reaches to `1 - η`, with
`0 < η ≤ H`. The exponential bounds the gain `(H / (H + η)) ^ (k + 1)`. -/
lemma norm_taylorCoeff_dslope_le {H η M : ℝ} (hη : 0 < η) (hηH : η ≤ H)
    (hF : ∀ s ∈ closedBall (1 + H : ℂ) (H + η), DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ M) (k : ℕ) :
    ‖(-H) ^ k * H / k ! * iteratedDeriv k (dslope F 1) (1 + H)‖ ≤
      4 * M * H / η * rexp (-((k + 1) * (η / (2 * H)))) := by
  have hH : 0 < H := hη.trans_le hηH
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF _ (mem_closedBall_self (by positivity))).right
  have h_ratio : H / (H + η) ≤ rexp (-(η / (2 * H))) :=
    calc H / (H + η) = 1 - η / (H + η) := by field
      _ ≤ 1 - η / (2 * H) := by
        gcongr
        linarith
      _ ≤ rexp (-(η / (2 * H))) := Real.one_sub_le_exp_neg _
  calc ‖(-H) ^ k * H / k ! * iteratedDeriv k (dslope F 1) (1 + H)‖
      = H ^ k * H / k ! * ‖iteratedDeriv k (dslope F 1) (1 + H)‖ := by simp [abs_of_pos hH]
    _ ≤ H ^ k * H / k ! * (k ! * (2 * M / η) / (H + η) ^ k) := by
        gcongr
        exact norm_iteratedDeriv_dslope_le hH.le hη hF k
    _ = 2 * M / η * (H + η) * (H / (H + η)) ^ (k + 1) := by
        rw [div_pow]
        field
    _ ≤ 2 * M / η * (H + H) * rexp (-(η / (2 * H))) ^ (k + 1) := by gcongr
    _ = 4 * M * H / η * rexp (-((k + 1) * (η / (2 * H)))) := by
        rw [← Real.exp_nat_mul, Nat.cast_succ]
        ring_nf

/-- If `|R v - R u| ≤ L (v - u)` for all steps `0 ≤ u ≤ v ≤ u + 1`, then `R` is Lipschitz with
constant `L` on `[0, ∞)`. -/
lemma abs_sub_le_of_unit_steps
    (h_step_le : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ u + 1 → |R v - R u| ≤ L * (v - u)) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) : |R v - R u| ≤ L * |v - u| := by
  wlog huv : u ≤ v generalizing u v with h_ordered
  · simpa only [abs_sub_comm] using h_ordered hv hu (le_of_not_ge huv)
  -- Cut the interval from `u` to `v` into `n` steps of length `t ≤ 1`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v - u < n := exists_nat_gt (v - u)
  have hn_pos : (0 : ℝ) < n := (sub_nonneg.2 huv).trans_lt hn
  let t : ℝ := (v - u) / n
  have ht_nonneg : 0 ≤ t := div_nonneg (sub_nonneg.2 huv) hn_pos.le
  have ht_le_one : t ≤ 1 := (div_le_one hn_pos).2 hn.le
  have h_step (i : ℕ) : dist (R (u + i * t)) (R (u + (i + 1 : ℕ) * t)) ≤ L * t := by
    rw [dist_comm, Real.dist_eq, Nat.cast_succ, add_one_mul, ← add_assoc]
    simpa using
      h_step_le (u + i * t) (u + i * t + t) (by positivity) (by linarith) (by linarith)
  calc |R v - R u| = dist (R (u + (0 : ℕ) * t)) (R (u + n * t)) := by
        simp [t, mul_div_cancel₀ _ hn_pos.ne', Real.dist_eq, abs_sub_comm]
    _ ≤ ∑ _ ∈ Finset.range n, L * t :=
        dist_le_range_sum_of_dist_le (f := fun i : ℕ ↦ R (u + i * t)) n fun _ ↦ h_step _
    _ = L * |v - u| := by simp [abs_of_nonneg (sub_nonneg.2 huv), t, field]

/-- Let `R` be measurable and Lipschitz with constant `L` on `[0, ∞)`, with transform
`Φ s = ∫₀^∞ R(v) e^{(1 - s) v} dv` in `re s > 2`, and let `u, δ > 0` and `H = (k + 1) / u > 1`. The
number `(-H) ^ k H Φ⁽ᵏ⁾(1 + H) / k!` is within `L (δ + u² / ((k + 1) δ))` of `R(u)`, because the
Gamma density has mean `u` and variance `u² / (k + 1)`. -/
lemma norm_taylorCoeff_transform_sub_le_of_lipschitz (hR : Measurable R)
    (h_lip : ∀ x : ℝ, 0 ≤ x → ∀ y : ℝ, 0 ≤ y → |R y - R x| ≤ L * |y - x|)
    (Φ_eq : ∀ s : ℂ, 2 < s.re → Φ s = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v))
    {u δ H : ℝ} {k : ℕ} (hu : 0 < u) (hδ : 0 < δ) (H_eq : H = (k + 1) / u) (hH : 1 < H) :
    ‖(-H) ^ k * H / k ! * iteratedDeriv k Φ (1 + H) - R u‖ ≤ L * (δ + u ^ 2 / (k + 1) / δ) := by
  have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (h_lip 0 le_rfl 1 zero_le_one)
  have R_le (v : ℝ) (hv : 0 ≤ v) : |R v| ≤ (|R 0| + L) * rexp v := by
    have h_sub : |R v - R 0| ≤ L * v := by simpa [abs_of_nonneg hv] using h_lip 0 le_rfl v hv
    nlinarith [abs_sub_abs_le_abs_sub (R v) (R 0), Real.add_one_le_exp v, abs_nonneg (R 0)]
  have h_near (v : ℝ) (hv : 0 < v) : |R v - R u| ≤ L * δ + L / δ * (v - (k + 1) / H) ^ 2 := by
    have h_amgm : |v - u| ≤ δ + (v - u) ^ 2 / δ := by
      field_simp
      nlinarith [sq_nonneg (|v - u| - δ), abs_nonneg (v - u), sq_abs (v - u)]
    rw [H_eq, div_div_cancel₀ (by positivity)]
    calc |R v - R u| ≤ L * |v - u| := h_lip u hu.le v hv.le
      _ ≤ L * (δ + (v - u) ^ 2 / δ) := by gcongr
      _ = L * δ + L / δ * (v - u) ^ 2 := by ring
  refine (norm_taylorCoeff_transform_sub_le hR R_le Φ_eq hH k h_near).trans_eq ?_
  rw [H_eq]
  field

/-- For large `u` an even power of `c log u` is at most `u`, and a power of `u` is at most
`exp (√u / 2)`. -/
lemma eventually_log_pow_le_and_pow_le_exp_sqrt (c : ℝ) (A j : ℕ) : ∀ᶠ u : ℝ in atTop,
    (c * u.log) ^ (2 * A) ≤ u ∧ u ^ j ≤ rexp (√u / 2) := by
  have h_log : (fun u : ℝ ↦ (c * u.log) ^ (2 * A)) =o[atTop] id := by
    simpa [mul_pow] using
      (Real.isLittleO_pow_log_id_atTop (n := 2 * A)).const_mul_left (c ^ (2 * A))
  have h_exp : ∀ᶠ t : ℝ in atTop, ‖t ^ (2 * j)‖ ≤ ‖rexp (2⁻¹ * t)‖ :=
    (isLittleO_pow_exp_pos_mul_atTop _ (by norm_num)).eventuallyLE
  filter_upwards [h_log.eventuallyLE, Real.tendsto_sqrt_atTop.eventually h_exp,
    eventually_ge_atTop 0] with u h_log_le h_exp_le hu
  refine ⟨(le_abs_self _).trans (h_log_le.trans_eq (abs_of_nonneg hu)), ?_⟩
  simpa [pow_mul, Real.sq_sqrt hu, abs_of_nonneg hu, div_eq_inv_mul] using h_exp_le

/-- Every point `s` of the disc of radius `H + η` about `1 + H` has `re s ≥ 1 - η` and
`|s| ≤ 2 H + η + 1`, for `H ≥ 0`. -/
lemma one_sub_le_re_and_norm_le_of_mem_closedBall {H η : ℝ} (hH : 0 ≤ H) {s : ℂ}
    (hs : s ∈ closedBall (1 + H : ℂ) (H + η)) : 1 - η ≤ s.re ∧ ‖s‖ ≤ 2 * H + η + 1 := by
  rw [mem_closedBall_iff_norm] at hs
  have h_re : |s.re - (1 + H)| ≤ H + η := by simpa using (abs_re_le_norm _).trans hs
  have h_centre : ‖(1 + H : ℂ)‖ = 1 + H := mod_cast Real.norm_of_nonneg (by linarith)
  exact ⟨by linarith [abs_le.1 h_re], by linarith [norm_le_norm_sub_add s (1 + H)]⟩

/-- Let `l ≥ 1`, let `H = (k + 1) / u > 1` with `4 H ≤ u ^ (2 B + 5)`, and let `F` be holomorphic
and at most `l ^ A` on the disc of radius `H + l ^ (-A)` about `1 + H`. If `l ^ (2 A) ≤ u` and
`u ^ (3 B + 7) ≤ exp (√u / 2)`, the normalised Taylor coefficient of `dslope F 1` at `1 + H` is at
most `u ^ (-(B + 1))`: the gain is `exp (-u / (2 l ^ A)) ≤ exp (-√u / 2)`. -/
lemma norm_taylorCoeff_dslope_le_inv_pow {u l H : ℝ} {A B k : ℕ} (hu : 0 < u) (hl : 1 ≤ l)
    (H_eq : H = (k + 1) / u) (hH : 1 < H) (hH_le : 4 * H ≤ u * u ^ (2 * B + 4))
    (h_pow : l ^ (2 * A) ≤ u) (h_exp : u ^ (3 * B + 7) ≤ rexp (√u / 2))
    (hF : ∀ s ∈ closedBall (1 + H : ℂ) (H + 1 / l ^ A), DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ l ^ A) :
    ‖(-H) ^ k * H / k ! * iteratedDeriv k (dslope F 1) (1 + H)‖ ≤ 1 / u ^ (B + 1) := by
  have hη_le : 1 / l ^ A ≤ H := by grw [← one_le_pow₀ hl, ← hH, div_one]
  have h_sqrt : l ^ A ≤ √u := Real.le_sqrt_of_sq_le (by rwa [← pow_mul, mul_comm])
  have h_gain : √u / 2 ≤ (k + 1) * (1 / l ^ A / (2 * H)) :=
    calc √u / 2 = u / √u / 2 := by rw [Real.div_sqrt]
      _ ≤ u / l ^ A / 2 := by gcongr
      _ = (k + 1) * (1 / l ^ A / (2 * H)) := by
        rw [H_eq]
        field
  calc ‖(-H) ^ k * H / k ! * iteratedDeriv k (dslope F 1) (1 + H)‖
      ≤ 4 * l ^ A * H / (1 / l ^ A) * rexp (-((k + 1) * (1 / l ^ A / (2 * H)))) :=
        norm_taylorCoeff_dslope_le (by positivity) hη_le hF k
    _ = l ^ (2 * A) * (4 * H) / rexp ((k + 1) * (1 / l ^ A / (2 * H))) := by
        rw [Real.exp_neg]
        field
    _ ≤ u * (u * u ^ (2 * B + 4)) / u ^ (3 * B + 7) := by
        grw [h_pow, hH_le, ← h_gain, ← h_exp]
    _ = 1 / u ^ (B + 1) := by field

/-- **Tauberian theorem.** Let `R` be measurable and Lipschitz on `v ≥ 0` (it suffices to test steps
of length at most `1`), with transform `∫₀^∞ R(v) e^{(1 - s) v} dv = (F s - F 1) / (s - 1)` in
`re s > 2`. Suppose that for all large `l` the function `F` is holomorphic and at most `l ^ A` on
`re s ≥ 1 - l ^ (-A)`, `|s| ≤ e ^ l`. Then `|R(u)| ≤ u ^ (-B)` for every `B` and all large `u`. -/
theorem eventually_abs_le_inv_pow_of_transform (hR : Measurable R)
    (h_lip : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ u + 1 → |R v - R u| ≤ L * (v - u))
    (h_transform : ∀ s : ℂ, 2 < s.re →
      (F s - F 1) / (s - 1) = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v)) {A : ℕ}
    (hF : ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ A ≤ s.re → ‖s‖ ≤ rexp l →
      DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ l ^ A) (B : ℕ) :
    ∀ᶠ u : ℝ in atTop, |R u| ≤ 1 / u ^ B := by
  have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (h_lip 0 1 le_rfl zero_le_one (by simp))
  have Φ_eq (s : ℂ) (hs : 2 < s.re) :
      dslope F 1 s = ∫ v in Ioi (0 : ℝ), R v * cexp ((1 - s) * v) := by
    have hs_ne : s ≠ 1 := fun h ↦ by norm_num [h] at hs
    rw [← h_transform s hs, dslope_of_ne _ hs_ne, slope_def_field]
  have h_log : Tendsto (fun u : ℝ ↦ (2 * B + 5 : ℕ) * u.log) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by positivity)
  -- Compare `R u` with one normalised Taylor coefficient of `dslope F 1` at a point `1 + H`: the
  -- two differ by `O(u ^ (-(B + 1)))`, and Cauchy's estimate makes the coefficient as small.
  filter_upwards [h_log.eventually hF, h_log.eventually_ge_atTop 1, eventually_ge_atTop (2 * L + 8),
    eventually_log_pow_le_and_pow_le_exp_sqrt (2 * B + 5 : ℕ) A (3 * B + 7)]
    with u hF_region hl_one hu_large ⟨h_log_pow_le, h_pow_le_exp⟩
  -- Take `k + 1 ≈ u ^ (2 B + 4)` and `H = (k + 1) / u`, so that the Gamma density has mean `u` and
  -- standard deviation `u / √(k + 1) ≤ u ^ (-(B + 1))`. With `l = (2 B + 5) log u` and
  -- `η = l ^ (-A)` the disc of radius `H + η` about `1 + H` lies in the region of `hF_region`.
  set l : ℝ := (2 * B + 5 : ℕ) * u.log with l_def
  have hu_one : 1 ≤ u := by linarith
  have hu_pos : 0 < u := one_pos.trans_le hu_one
  let k : ℕ := ⌊u ^ (2 * B + 4)⌋₊
  have hk_ge : u ^ (2 * B + 4) ≤ k + 1 := (Nat.lt_floor_add_one _).le
  have hk_le : (k : ℝ) ≤ u ^ (2 * B + 4) := Nat.floor_le (by positivity)
  let H : ℝ := (k + 1) / u
  have hH_gt : 1 < H :=
    (one_lt_div hu_pos).2 ((lt_self_pow₀ (by linarith) (by omega)).trans_le hk_ge)
  have hH_le : H ≤ 2 * u ^ (2 * B + 4) :=
    (div_le_self (by positivity) hu_one).trans (by linarith [one_le_pow₀ hu_one (n := 2 * B + 4)])
  let η : ℝ := 1 / l ^ A
  have hη_le : η ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ hl_one)
  let coeff : ℂ := (-H) ^ k * H / k ! * iteratedDeriv k (dslope F 1) (1 + H)
  -- As `u ≥ 8`, the factor `u` absorbs the numerical constants below.
  have h_const_mul_le : 8 * u ^ (2 * B + 4) ≤ u * u ^ (2 * B + 4) := by nlinarith
  have h_close : ‖coeff - R u‖ ≤ 2 * L / u ^ (B + 1) :=
    calc ‖coeff - R u‖ ≤ L * (1 / u ^ (B + 1) + u ^ 2 / (k + 1) / (1 / u ^ (B + 1))) :=
          norm_taylorCoeff_transform_sub_le_of_lipschitz hR
            (fun x hx y hy ↦ abs_sub_le_of_unit_steps h_lip hx hy) Φ_eq hu_pos (by positivity)
            rfl hH_gt
      _ ≤ L * (1 / u ^ (B + 1) + u ^ 2 / u ^ (2 * B + 4) / (1 / u ^ (B + 1))) := by gcongr
      _ = 2 * L / u ^ (B + 1) := by field
  have h_disc (s : ℂ) (hs : s ∈ closedBall (1 + H : ℂ) (H + η)) :
      DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ l ^ A := by
    obtain ⟨h_re, h_norm⟩ := one_sub_le_re_and_norm_le_of_mem_closedBall (by positivity) hs
    refine hF_region s h_re (h_norm.trans ?_)
    rw [l_def, Real.exp_nat_mul, Real.exp_log hu_pos, pow_succ']
    linarith
  have h_small : ‖coeff‖ ≤ 1 / u ^ (B + 1) :=
    norm_taylorCoeff_dslope_le_inv_pow hu_pos hl_one rfl hH_gt (by linarith) h_log_pow_le
      h_pow_le_exp h_disc
  calc |R u| = ‖coeff - (coeff - R u)‖ := by simp
    _ ≤ 1 / u ^ (B + 1) + 2 * L / u ^ (B + 1) := norm_sub_le_of_le h_small h_close
    _ = (1 + 2 * L) / u / u ^ B := by field
    _ ≤ 1 / u ^ B := by grw [(div_le_one hu_pos).2 (by linarith : 1 + 2 * L ≤ u)]

end New
