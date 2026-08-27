import FabiusFunction.DoublingTransferAdjoint

/-!
# The weighted transfer step and the `√2/2` sup bound

First components of the audits' Ruelle–Perron–Frobenius layer, both
exact and elementary:

* **The transfer identity, one step** (`eq:transfer-identity`, `n = 1`):
  because `sin (πx/2) = s(x/2)` and `sin (π(x+1)/2) = cos (πx/2)` with
  `s(t) = |sin πt|`, the weighted operator
  `(𝓛_q h)(x) = ½(sin^q(πx/2)·h(x/2) + cos^q(πx/2)·h((x+1)/2))`
  is the unweighted Perron operator applied to `s^q·h`, so its
  integral telescopes to the weighted mean:
  `∫₀¹ 𝓛_q h = ∫₀¹ s^q·h`.  Iterated, this is the audit's
  `∫₀¹ h·Pₙ^q = ∫₀¹ 𝓛_qⁿ h`, the bridge between Birkhoff products and
  transfer powers.
* **The `√2/2` sup bound** (Document 7's Lasota–Yorke architecture):
  `|sin θ| + |cos θ| ≤ √2` pointwise, hence
  `|(𝓛₁h)(x)| ≤ (√2/2)·‖h‖∞` on `[0,1]` — the sup-norm half of the
  essential-spectral-radius estimate that isolates the Perron root
  `ϱ₁ ≥ 3^{-1/2} > √2/4`.

* `abs_sin_add_abs_cos_le` — `|sin θ| + |cos θ| ≤ √2`.
* `integral_transfer_step` — the one-step transfer identity.
* `transfer_step_abs_le` — the pointwise `√2/2` bound for `𝓛₁`.
-/

set_option autoImplicit false

open Real intervalIntegral

namespace Fabius

/-- `|sin θ| + |cos θ| ≤ √2`, for every real `θ`. -/
theorem abs_sin_add_abs_cos_le (θ : ℝ) :
    |Real.sin θ| + |Real.cos θ| ≤ Real.sqrt 2 := by
  have hpy := Real.sin_sq_add_cos_sq θ
  have hL0 : 0 ≤ |Real.sin θ| + |Real.cos θ| := by positivity
  have hR0 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine le_of_pow_le_pow_left₀ (by norm_num : (2:ℕ) ≠ 0) hR0 ?_
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsq : (|Real.sin θ| + |Real.cos θ|) ^ 2 =
      1 + 2 * (|Real.sin θ| * |Real.cos θ|) := by
    have h1 : |Real.sin θ| ^ 2 = Real.sin θ ^ 2 := sq_abs _
    have h2 : |Real.cos θ| ^ 2 = Real.cos θ ^ 2 := sq_abs _
    nlinarith [h1, h2, hpy]
  rw [hsq]
  nlinarith [sq_nonneg (|Real.sin θ| - |Real.cos θ|), sq_abs (Real.sin θ),
    sq_abs (Real.cos θ), hpy]

/-- **The transfer identity, one step**: for continuous `h` and any
weight exponent `q`, the integral of the weighted transfer operator is
the weighted mean,
`∫₀¹ ½(w(x/2)·h(x/2) + w((x+1)/2)·h((x+1)/2)) dx = ∫₀¹ w·h` with
`w(t) = |sin πt|^q`.  This is `∫ 𝓛_q h = ∫ s^q·h` — the `n = 1` case
of the audit's `∫ h·Pₙ^q = ∫ 𝓛_qⁿ h`. -/
theorem integral_transfer_step (h : ℝ → ℝ) (hh : Continuous h) (q : ℕ) :
    ∫ x in (0:ℝ)..1,
      (|Real.sin (π * (x / 2))| ^ q * h (x / 2) +
        |Real.sin (π * ((x + 1) / 2))| ^ q * h ((x + 1) / 2)) / 2 =
    ∫ t in (0:ℝ)..1, |Real.sin (π * t)| ^ q * h t := by
  have hf : Continuous fun t : ℝ => |Real.sin (π * t)| ^ q * h t := by
    fun_prop
  have hadj := integral_mul_comp_doubling
    (fun t => |Real.sin (π * t)| ^ q * h t) (fun _ => 1) hf continuous_const
  simp only [mul_one] at hadj
  have hsplit : ((∫ t in (0:ℝ)..(1/2:ℝ),
        |Real.sin (π * t)| ^ q * h t) +
      ∫ t in (1/2:ℝ)..1, |Real.sin (π * t)| ^ q * h t) =
      ∫ t in (0:ℝ)..1, |Real.sin (π * t)| ^ q * h t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 (1/2)) (hf.intervalIntegrable (1/2) 1)
  rw [← hsplit, ← hadj]

/-- **The `√2/2` sup bound for the arithmetic transfer operator**: if
`|h| ≤ M` everywhere then
`|½(sin(πx/2)·h(x/2) + cos(πx/2)·h((x+1)/2))| ≤ (√2/2)·M` — in fact
for every real `x` — the sup-norm half of Document 7's Lasota–Yorke
estimate. -/
theorem transfer_step_abs_le (h : ℝ → ℝ) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (x : ℝ) :
    |(Real.sin (π * x / 2) * h (x / 2) +
        Real.cos (π * x / 2) * h ((x + 1) / 2)) / 2| ≤
      Real.sqrt 2 / 2 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have htri : |Real.sin (π * x / 2) * h (x / 2) +
      Real.cos (π * x / 2) * h ((x + 1) / 2)| ≤
      |Real.sin (π * x / 2)| * M + |Real.cos (π * x / 2)| * M := by
    calc |Real.sin (π * x / 2) * h (x / 2) +
          Real.cos (π * x / 2) * h ((x + 1) / 2)|
        ≤ |Real.sin (π * x / 2) * h (x / 2)| +
            |Real.cos (π * x / 2) * h ((x + 1) / 2)| := abs_add_le _ _
      _ ≤ |Real.sin (π * x / 2)| * M + |Real.cos (π * x / 2)| * M := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact hM _
          · exact hM _
  have hsc := abs_sin_add_abs_cos_le (π * x / 2)
  rw [abs_div]
  rw [show |(2:ℝ)| = 2 by norm_num]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  calc |Real.sin (π * x / 2) * h (x / 2) +
        Real.cos (π * x / 2) * h ((x + 1) / 2)|
      ≤ |Real.sin (π * x / 2)| * M + |Real.cos (π * x / 2)| * M := htri
    _ = (|Real.sin (π * x / 2)| + |Real.cos (π * x / 2)|) * M := by ring
    _ ≤ Real.sqrt 2 * M := by
        exact mul_le_mul_of_nonneg_right hsc hM0
    _ = Real.sqrt 2 / 2 * M * 2 := by ring

/-- **The Lipschitz half of the Lasota–Yorke estimate** (Document 7):
if `φ` has Lipschitz constant `L` and sup bound `M`, then for
`y ∈ [0,1]` and any `x`,
`|𝓛₁φ(x) - 𝓛₁φ(y)| ≤ (√2/4·L + π/2·M)·|x-y|` — the Lipschitz
seminorm contracts by `√2/4` modulo a `‖φ‖∞` term.  With
`transfer_step_abs_le` this is the full Lasota–Yorke inequality whose
essential-radius bound `√2/4 < 3^{-1/2} ≤ ϱ₁` isolates the Perron
root. -/
theorem transfer_step_lipschitz (φ : ℝ → ℝ) {L M : ℝ}
    (hL : ∀ a b, |φ a - φ b| ≤ L * |a - b|)
    (hM : ∀ y, |φ y| ≤ M) {x y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(Real.sin (π * x / 2) * φ (x / 2) +
        Real.cos (π * x / 2) * φ ((x + 1) / 2)) / 2 -
      (Real.sin (π * y / 2) * φ (y / 2) +
        Real.cos (π * y / 2) * φ ((y + 1) / 2)) / 2| ≤
      (Real.sqrt 2 / 4 * L + π / 2 * M) * |x - y| := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hL0 : 0 ≤ L := by
    have h := hL 0 1
    have h2 : |(0:ℝ) - 1| = 1 := by norm_num
    rw [h2, mul_one] at h
    linarith [abs_nonneg (φ 0 - φ 1)]
  set A : ℝ := (Real.sin (π * x / 2) - Real.sin (π * y / 2)) * φ (x / 2)
    with hA_def
  set B : ℝ := Real.sin (π * y / 2) * (φ (x / 2) - φ (y / 2)) with hB_def
  set C : ℝ := (Real.cos (π * x / 2) - Real.cos (π * y / 2)) *
    φ ((x + 1) / 2) with hC_def
  set D : ℝ := Real.cos (π * y / 2) *
    (φ ((x + 1) / 2) - φ ((y + 1) / 2)) with hD_def
  have hdecomp : (Real.sin (π * x / 2) * φ (x / 2) +
        Real.cos (π * x / 2) * φ ((x + 1) / 2)) / 2 -
      (Real.sin (π * y / 2) * φ (y / 2) +
        Real.cos (π * y / 2) * φ ((y + 1) / 2)) / 2 =
      (A + B + (C + D)) / 2 := by
    rw [hA_def, hB_def, hC_def, hD_def]
    ring
  have hsin_diff : |Real.sin (π * x / 2) - Real.sin (π * y / 2)| ≤
      π / 2 * |x - y| := by
    calc |Real.sin (π * x / 2) - Real.sin (π * y / 2)|
        ≤ |π * x / 2 - π * y / 2| := Real.abs_sin_sub_sin_le _ _
      _ = π / 2 * |x - y| := by
          rw [show π * x / 2 - π * y / 2 = π / 2 * (x - y) by ring, abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < π / 2)]
  have hcos_diff : |Real.cos (π * x / 2) - Real.cos (π * y / 2)| ≤
      π / 2 * |x - y| := by
    calc |Real.cos (π * x / 2) - Real.cos (π * y / 2)|
        ≤ |π * x / 2 - π * y / 2| := Real.abs_cos_sub_cos_le _ _
      _ = π / 2 * |x - y| := by
          rw [show π * x / 2 - π * y / 2 = π / 2 * (x - y) by ring, abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < π / 2)]
  have hφ1 : |φ (x / 2) - φ (y / 2)| ≤ L * |x - y| / 2 := by
    calc |φ (x / 2) - φ (y / 2)| ≤ L * |x / 2 - y / 2| := hL _ _
      _ = L * |x - y| / 2 := by
          rw [show x / 2 - y / 2 = (x - y) / 2 by ring, abs_div,
            abs_of_pos (by norm_num : (0:ℝ) < 2)]
          ring
  have hφ2 : |φ ((x + 1) / 2) - φ ((y + 1) / 2)| ≤ L * |x - y| / 2 := by
    calc |φ ((x + 1) / 2) - φ ((y + 1) / 2)|
        ≤ L * |(x + 1) / 2 - (y + 1) / 2| := hL _ _
      _ = L * |x - y| / 2 := by
          rw [show (x + 1) / 2 - (y + 1) / 2 = (x - y) / 2 by ring, abs_div,
            abs_of_pos (by norm_num : (0:ℝ) < 2)]
          ring
  have hsy : 0 ≤ Real.sin (π * y / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · have := Real.pi_pos
      nlinarith
    · nlinarith [Real.pi_pos]
  have hcy : 0 ≤ Real.cos (π * y / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hsc := abs_sin_add_abs_cos_le (π * y / 2)
  rw [abs_of_nonneg hsy, abs_of_nonneg hcy] at hsc
  have hAb : |A| ≤ π / 2 * |x - y| * M := by
    rw [hA_def, abs_mul]
    exact mul_le_mul hsin_diff (hM _) (abs_nonneg _) (by positivity)
  have hBb : |B| ≤ Real.sin (π * y / 2) * (L * |x - y| / 2) := by
    rw [hB_def, abs_mul, abs_of_nonneg hsy]
    exact mul_le_mul_of_nonneg_left hφ1 hsy
  have hCb : |C| ≤ π / 2 * |x - y| * M := by
    rw [hC_def, abs_mul]
    exact mul_le_mul hcos_diff (hM _) (abs_nonneg _) (by positivity)
  have hDb : |D| ≤ Real.cos (π * y / 2) * (L * |x - y| / 2) := by
    rw [hD_def, abs_mul, abs_of_nonneg hcy]
    exact mul_le_mul_of_nonneg_left hφ2 hcy
  rw [hdecomp, abs_div, show |(2:ℝ)| = 2 by norm_num,
    div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have htri : |A + B + (C + D)| ≤ |A| + |B| + (|C| + |D|) := by
    calc |A + B + (C + D)| ≤ |A + B| + |C + D| := abs_add_le _ _
      _ ≤ |A| + |B| + (|C| + |D|) :=
          add_le_add (abs_add_le _ _) (abs_add_le _ _)
  have hLxy : 0 ≤ L * |x - y| / 2 := by positivity
  calc |A + B + (C + D)| ≤ |A| + |B| + (|C| + |D|) := htri
    _ ≤ (π / 2 * |x - y| * M + Real.sin (π * y / 2) * (L * |x - y| / 2)) +
        (π / 2 * |x - y| * M + Real.cos (π * y / 2) * (L * |x - y| / 2)) :=
        add_le_add (add_le_add hAb hBb) (add_le_add hCb hDb)
    _ = π * |x - y| * M +
        (Real.sin (π * y / 2) + Real.cos (π * y / 2)) * (L * |x - y| / 2) := by
        ring
    _ ≤ π * |x - y| * M + Real.sqrt 2 * (L * |x - y| / 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hsc hLxy)
    _ = (Real.sqrt 2 / 4 * L + π / 2 * M) * |x - y| * 2 := by
        ring

end Fabius
