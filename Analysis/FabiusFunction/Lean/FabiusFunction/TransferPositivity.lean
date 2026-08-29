import FabiusFunction.TransferOperatorStep

/-!
# The arithmetic transfer operator: positivity toolkit

The transfer operator of the audits' RPF layer as a definition,

`(𝓛 h)(x) = (sin (πx/2)·h(x/2) + cos (πx/2)·h((x+1)/2))/2`,

with the order-theoretic facts that drive the Perron–Frobenius
analysis on `[0,1]`: the two branch weights are nonnegative there and
sum to at least `1` and at most `√2`, so `𝓛` is positive, monotone,
homogeneous, and its iterates applied to `𝟙` are bracketed by

`(1/2)ⁿ ≤ 𝓛ⁿ𝟙 ≤ (√2/2)ⁿ`  on `[0,1]`.

These are the inputs to the Fekete existence of the Perron root in
`PerronRootExistence`.

* `sin_half_nonneg`, `cos_half_nonneg`, `one_le_sin_add_cos_half`,
  `sin_add_cos_half_le` — the weight bracket `1 ≤ s + c ≤ √2`.
* `rpfTransfer_nonneg`, `rpfTransfer_mono`, `rpfTransfer_const_mul` —
  positivity, monotonicity, homogeneity.
* `rpfTransfer_le_of_le`, `le_rpfTransfer_of_le` — one-step bounds.
* `iterate_rpfTransfer_one_le`, `le_iterate_rpfTransfer_one` — the
  iterate bracket.
* `continuous_rpfTransfer`, `continuous_iterate_rpfTransfer_one`.
-/

set_option autoImplicit false

open Real Set

namespace Fabius

/-- The arithmetic transfer operator of the RPF layer. -/
noncomputable def rpfTransfer (h : ℝ → ℝ) : ℝ → ℝ := fun x =>
  (Real.sin (π * x / 2) * h (x / 2) +
    Real.cos (π * x / 2) * h ((x + 1) / 2)) / 2

/-- Expands the arithmetic transfer operator at a point. -/
theorem rpfTransfer_apply (h : ℝ → ℝ) (x : ℝ) :
    rpfTransfer h x = (Real.sin (π * x / 2) * h (x / 2) +
      Real.cos (π * x / 2) * h ((x + 1) / 2)) / 2 := rfl

/-- The left branch weight is nonnegative on `[0,1]`. -/
theorem sin_half_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ Real.sin (π * x / 2) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · have := Real.pi_pos
    have := hx.1
    positivity
  · nlinarith [Real.pi_pos, hx.2]

/-- The right branch weight is nonnegative on `[0,1]`. -/
theorem cos_half_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ Real.cos (π * x / 2) := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · nlinarith [Real.pi_pos, hx.1]
  · nlinarith [Real.pi_pos, hx.2]

/-- On `[0,1]` the branch weights sum to at least `1`. -/
theorem one_le_sin_add_cos_half {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    1 ≤ Real.sin (π * x / 2) + Real.cos (π * x / 2) := by
  have hs := sin_half_nonneg hx
  have hc := cos_half_nonneg hx
  have hpy := Real.sin_sq_add_cos_sq (π * x / 2)
  nlinarith [mul_nonneg hs hc]

/-- On any point the branch weights sum to at most `√2`. -/
theorem sin_add_cos_half_le (x : ℝ) :
    Real.sin (π * x / 2) + Real.cos (π * x / 2) ≤ Real.sqrt 2 := by
  have h1 : Real.sin (π * x / 2) ≤ |Real.sin (π * x / 2)| :=
    le_abs_self _
  have h2 : Real.cos (π * x / 2) ≤ |Real.cos (π * x / 2)| :=
    le_abs_self _
  have h3 : |Real.sin (π * x / 2)| + |Real.cos (π * x / 2)| ≤
      Real.sqrt 2 := abs_sin_add_abs_cos_le _
  linarith

/-- The two branch points of `x ∈ [0,1]` stay in `[0,1]`. -/
theorem branch_left_mem {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    x / 2 ∈ Set.Icc (0:ℝ) 1 :=
  ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The right branch point `(x + 1) / 2` stays in `[0,1]`. -/
theorem branch_right_mem {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (x + 1) / 2 ∈ Set.Icc (0:ℝ) 1 :=
  ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **Positivity**: `𝓛` preserves nonnegativity on `[0,1]`. -/
theorem rpfTransfer_nonneg {h : ℝ → ℝ}
    (hh : ∀ y ∈ Set.Icc (0:ℝ) 1, 0 ≤ h y) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ rpfTransfer h x := by
  rw [rpfTransfer_apply]
  have h1 := mul_nonneg (sin_half_nonneg hx) (hh _ (branch_left_mem hx))
  have h2 := mul_nonneg (cos_half_nonneg hx) (hh _ (branch_right_mem hx))
  linarith

/-- **Monotonicity**: `𝓛` preserves pointwise order on `[0,1]`. -/
theorem rpfTransfer_mono {h g : ℝ → ℝ}
    (hle : ∀ y ∈ Set.Icc (0:ℝ) 1, h y ≤ g y) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    rpfTransfer h x ≤ rpfTransfer g x := by
  rw [rpfTransfer_apply, rpfTransfer_apply]
  have h1 := mul_le_mul_of_nonneg_left (hle _ (branch_left_mem hx))
    (sin_half_nonneg hx)
  have h2 := mul_le_mul_of_nonneg_left (hle _ (branch_right_mem hx))
    (cos_half_nonneg hx)
  linarith

/-- **Homogeneity**: `𝓛(c·h) = c·𝓛h`. -/
theorem rpfTransfer_const_mul (c : ℝ) (h : ℝ → ℝ) (x : ℝ) :
    rpfTransfer (fun y => c * h y) x = c * rpfTransfer h x := by
  rw [rpfTransfer_apply, rpfTransfer_apply]
  ring

/-- **One-step upper bound**: `h ≤ M` on `[0,1]` with `0 ≤ M` gives
`𝓛h ≤ (√2/2)·M` on `[0,1]`. -/
theorem rpfTransfer_le_of_le {h : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hle : ∀ y ∈ Set.Icc (0:ℝ) 1, h y ≤ M) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    rpfTransfer h x ≤ Real.sqrt 2 / 2 * M := by
  rw [rpfTransfer_apply]
  have h1 := mul_le_mul_of_nonneg_left (hle _ (branch_left_mem hx))
    (sin_half_nonneg hx)
  have h2 := mul_le_mul_of_nonneg_left (hle _ (branch_right_mem hx))
    (cos_half_nonneg hx)
  have h3 := sin_add_cos_half_le x
  nlinarith

/-- **One-step lower bound**: `m ≤ h` on `[0,1]` with `0 ≤ m` gives
`m/2 ≤ 𝓛h` on `[0,1]`. -/
theorem le_rpfTransfer_of_le {h : ℝ → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hle : ∀ y ∈ Set.Icc (0:ℝ) 1, m ≤ h y) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    m / 2 ≤ rpfTransfer h x := by
  rw [rpfTransfer_apply]
  have h1 := mul_le_mul_of_nonneg_left (hle _ (branch_left_mem hx))
    (sin_half_nonneg hx)
  have h2 := mul_le_mul_of_nonneg_left (hle _ (branch_right_mem hx))
    (cos_half_nonneg hx)
  have h3 := one_le_sin_add_cos_half hx
  nlinarith [mul_le_mul_of_nonneg_right h3 hm]

/-- The iterates of `𝟙` stay nonnegative on `[0,1]`. -/
theorem iterate_rpfTransfer_one_nonneg (n : ℕ) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ (rpfTransfer^[n] (fun _ => 1)) x := by
  induction n with
  | zero =>
      intro x _
      simp
  | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact rpfTransfer_nonneg ih hx

/-- **Iterate upper bound**: `𝓛ⁿ𝟙 ≤ (√2/2)ⁿ` on `[0,1]`. -/
theorem iterate_rpfTransfer_one_le (n : ℕ) :
    ∀ x ∈ Set.Icc (0:ℝ) 1,
      (rpfTransfer^[n] (fun _ => 1)) x ≤ (Real.sqrt 2 / 2) ^ n := by
  induction n with
  | zero =>
      intro x _
      simp
  | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      calc rpfTransfer (rpfTransfer^[n] (fun _ => 1)) x
          ≤ Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) ^ n :=
            rpfTransfer_le_of_le (by positivity) ih hx
        _ = (Real.sqrt 2 / 2) ^ (n + 1) := by ring

/-- **Iterate lower bound**: `(1/2)ⁿ ≤ 𝓛ⁿ𝟙` on `[0,1]`. -/
theorem le_iterate_rpfTransfer_one (n : ℕ) :
    ∀ x ∈ Set.Icc (0:ℝ) 1,
      (1 / 2 : ℝ) ^ n ≤ (rpfTransfer^[n] (fun _ => 1)) x := by
  induction n with
  | zero =>
      intro x _
      simp
  | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      have h := le_rpfTransfer_of_le (by positivity) ih hx
      calc ((1:ℝ) / 2) ^ (n + 1) = (1 / 2 : ℝ) ^ n / 2 := by ring
        _ ≤ rpfTransfer (rpfTransfer^[n] (fun _ => 1)) x := h

/-- `𝓛` preserves continuity. -/
theorem continuous_rpfTransfer {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (rpfTransfer h) := by
  unfold rpfTransfer
  fun_prop

/-- The iterates of `𝟙` are continuous. -/
theorem continuous_iterate_rpfTransfer_one (n : ℕ) :
    Continuous (rpfTransfer^[n] (fun _ => 1)) := by
  induction n with
  | zero =>
      simpa using continuous_const
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact continuous_rpfTransfer ih

end Fabius
