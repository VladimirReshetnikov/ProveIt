import FabiusFunction.TransferPositivity
import Mathlib.Analysis.Subadditive

/-!
# Existence of the Perron root of the transfer operator

The growth rate of the transfer iterates **exists**: with
`aₙ := sup_{[0,1]} 𝓛ⁿ𝟙`, positivity and monotonicity of `𝓛` make the
sequence submultiplicative, so Fekete's lemma applies to `log aₙ` and

`ρ₁ := lim aₙ^{1/n}`

exists, with the kernel-verified bracket `1/2 ≤ ρ₁ ≤ √2/2` from the
iterate bracket of `TransferPositivity`.  This unique growth-root limit
is the audits' Perron root as a *formal object*.  Identifying it with the
spectral radius of `𝓛` on `C[0,1]`, proving an eigenfunction, and obtaining
the refined value `ρ₁ = 0.66132…` remain parts of the RPF program.

* `transferSup` — `aₙ`.
* `transferSup_pos`, `transferSup_le`, `transferSup_submul` — the
  bracket and submultiplicativity.
* `exists_perron_exponent` — Fekete: `log aₙ/n` converges, with
  `−log 2 ≤ L ≤ log (√2/2)`.
* `exists_perron_root`, `existsUnique_perron_root` — the bracketed growth-root
  limit exists and is unique.
-/

set_option autoImplicit false

open Real Set Filter Topology

namespace Fabius

/-- The sup of the transfer iterate `𝓛ⁿ𝟙` over `[0,1]`. -/
noncomputable def transferSup (n : ℕ) : ℝ :=
  sSup ((rpfTransfer^[n] (fun _ => 1)) '' Set.Icc 0 1)

/-- The compact continuous image defining `transferSup n` is bounded above. -/
theorem transferSup_bddAbove (n : ℕ) :
    BddAbove ((rpfTransfer^[n] (fun _ => (1:ℝ))) '' Set.Icc 0 1) :=
  (isCompact_Icc.image_of_continuousOn
    (continuous_iterate_rpfTransfer_one n).continuousOn).bddAbove

/-- The image defining `transferSup n` is nonempty because `[0,1]` is nonempty. -/
theorem transferSup_image_nonempty (n : ℕ) :
    ((rpfTransfer^[n] (fun _ => (1:ℝ))) '' Set.Icc 0 1).Nonempty :=
  (Set.nonempty_Icc.mpr zero_le_one).image _

/-- Pointwise domination by the sup. -/
theorem apply_le_transferSup (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (rpfTransfer^[n] (fun _ => 1)) x ≤ transferSup n :=
  le_csSup (transferSup_bddAbove n) (Set.mem_image_of_mem _ hx)

/-- The supremum is attained by the `n`th transfer iterate at some point of `[0,1]`. -/
theorem exists_apply_eq_transferSup (n : ℕ) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1,
      (rpfTransfer^[n] (fun _ => 1)) x = transferSup n := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one)
    (continuous_iterate_rpfTransfer_one n).continuousOn
  refine ⟨x, hx, le_antisymm (apply_le_transferSup n hx) ?_⟩
  apply csSup_le (transferSup_image_nonempty n)
  rintro y ⟨z, hz, rfl⟩
  exact hmax hz

/-- The lower half of the bracket: `(1/2)ⁿ ≤ aₙ`. -/
theorem le_transferSup (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ transferSup n :=
  le_trans (le_iterate_rpfTransfer_one n 0 (by norm_num))
    (apply_le_transferSup n (by norm_num))

/-- The upper half of the bracket: `aₙ ≤ (√2/2)ⁿ`. -/
theorem transferSup_le (n : ℕ) :
    transferSup n ≤ (Real.sqrt 2 / 2) ^ n := by
  apply csSup_le (transferSup_image_nonempty n)
  rintro y ⟨x, hx, rfl⟩
  exact iterate_rpfTransfer_one_le n x hx

/-- The transfer supremum is strictly positive for every iterate. -/
theorem transferSup_pos (n : ℕ) : 0 < transferSup n :=
  lt_of_lt_of_le (by positivity) (le_transferSup n)

/-- Iterated monotonicity of `𝓛` on `[0,1]`. -/
theorem iterate_rpfTransfer_mono {h g : ℝ → ℝ} (m : ℕ)
    (hle : ∀ y ∈ Set.Icc (0:ℝ) 1, h y ≤ g y) :
    ∀ x ∈ Set.Icc (0:ℝ) 1,
      (rpfTransfer^[m] h) x ≤ (rpfTransfer^[m] g) x := by
  induction m with
  | zero => exact hle
  | succ m ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact rpfTransfer_mono ih hx

/-- Iterated homogeneity of `𝓛`. -/
theorem iterate_rpfTransfer_const_mul (c : ℝ) (h : ℝ → ℝ) (m : ℕ) :
    rpfTransfer^[m] (fun y => c * h y) =
      fun x => c * (rpfTransfer^[m] h) x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext x
      exact rpfTransfer_const_mul c (rpfTransfer^[m] h) x

/-- **Submultiplicativity**: `a_{m+n} ≤ aₘ·aₙ`. -/
theorem transferSup_submul (m n : ℕ) :
    transferSup (m + n) ≤ transferSup m * transferSup n := by
  apply csSup_le (transferSup_image_nonempty (m + n))
  rintro y ⟨x, hx, rfl⟩
  rw [Function.iterate_add_apply]
  have h1 : ∀ z ∈ Set.Icc (0:ℝ) 1,
      (rpfTransfer^[n] (fun _ => (1:ℝ))) z ≤
        transferSup n * 1 := by
    intro z hz
    rw [mul_one]
    exact apply_le_transferSup n hz
  have h2 : (rpfTransfer^[m] (rpfTransfer^[n] (fun _ => (1:ℝ)))) x ≤
      (rpfTransfer^[m] (fun y => transferSup n * 1)) x := by
    apply iterate_rpfTransfer_mono m h1 x hx
  have h3 : (rpfTransfer^[m] (fun _ => transferSup n * 1)) x =
      transferSup n * (rpfTransfer^[m] (fun _ => 1)) x := by
    have := iterate_rpfTransfer_const_mul (transferSup n)
      (fun _ => (1:ℝ)) m
    calc (rpfTransfer^[m] (fun _ => transferSup n * 1)) x
        = (rpfTransfer^[m] (fun _ => transferSup n * (1:ℝ))) x := rfl
      _ = transferSup n * (rpfTransfer^[m] (fun _ => 1)) x := by
          rw [this]
  calc (rpfTransfer^[m] (rpfTransfer^[n] (fun _ => (1:ℝ)))) x
      ≤ (rpfTransfer^[m] (fun _ => transferSup n * 1)) x := h2
    _ = transferSup n * (rpfTransfer^[m] (fun _ => 1)) x := h3
    _ ≤ transferSup n * transferSup m :=
        mul_le_mul_of_nonneg_left (apply_le_transferSup m hx)
          (transferSup_pos n).le
    _ = transferSup m * transferSup n := mul_comm _ _

/-- **Fekete for the transfer operator**: the log-growth rate of the
iterates exists, with `−log 2 ≤ L ≤ log (√2/2)`. -/
theorem exists_perron_exponent :
    ∃ L : ℝ, -Real.log 2 ≤ L ∧ L ≤ Real.log (Real.sqrt 2 / 2) ∧
      Tendsto (fun n : ℕ => Real.log (transferSup n) / n)
        atTop (𝓝 L) := by
  have hsub : Subadditive (fun n => Real.log (transferSup n)) := by
    intro m n
    calc Real.log (transferSup (m + n)) ≤
        Real.log (transferSup m * transferSup n) :=
          Real.log_le_log (transferSup_pos _) (transferSup_submul m n)
      _ = Real.log (transferSup m) + Real.log (transferSup n) :=
          Real.log_mul (transferSup_pos m).ne' (transferSup_pos n).ne'
  have hlow : ∀ n : ℕ, 1 ≤ n →
      -Real.log 2 ≤ Real.log (transferSup n) / n := by
    intro n hn
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ))]
    have h1 : ((1:ℝ) / 2) ^ n ≤ transferSup n := le_transferSup n
    have h2 : Real.log ((1 / 2 : ℝ) ^ n) ≤ Real.log (transferSup n) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have h3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [h3] at h2
    calc -Real.log 2 * n = (n : ℝ) * (-Real.log 2) := by ring
      _ ≤ Real.log (transferSup n) := h2
  have hup : ∀ n : ℕ, 1 ≤ n →
      Real.log (transferSup n) / n ≤ Real.log (Real.sqrt 2 / 2) := by
    intro n hn
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ))]
    have h1 : transferSup n ≤ (Real.sqrt 2 / 2) ^ n := transferSup_le n
    have h2 : Real.log (transferSup n) ≤
        Real.log ((Real.sqrt 2 / 2) ^ n) :=
      Real.log_le_log (transferSup_pos n) h1
    rw [Real.log_pow] at h2
    calc Real.log (transferSup n) ≤
        (n : ℝ) * Real.log (Real.sqrt 2 / 2) := h2
      _ = Real.log (Real.sqrt 2 / 2) * n := by ring
  have hbdd : BddBelow (Set.range
      (fun n : ℕ => Real.log (transferSup n) / n)) := by
    refine ⟨-Real.log 2, ?_⟩
    rintro y ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, div_zero]
      have := Real.log_pos (by norm_num : (1:ℝ) < 2)
      linarith
    · exact hlow n hn
  refine ⟨hsub.lim, ?_, ?_, hsub.tendsto_lim hbdd⟩
  · apply ge_of_tendsto (hsub.tendsto_lim hbdd)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hlow n hn
  · apply le_of_tendsto (hsub.tendsto_lim hbdd)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hup n hn

/-- **Existence of the Perron root**: `aₙ^{1/n}` converges to some
`ρ ∈ [1/2, √2/2]` — the audits' `ρ₁` as a formal object. -/
theorem exists_perron_root :
    ∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ ≤ Real.sqrt 2 / 2 ∧
      Tendsto (fun n : ℕ => (transferSup n) ^ ((1:ℝ) / n))
        atTop (𝓝 ρ) := by
  obtain ⟨L, hL1, hL2, hLt⟩ := exists_perron_exponent
  refine ⟨Real.exp L, ?_, ?_, ?_⟩
  · have hexp : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      norm_num
    calc (1:ℝ) / 2 = Real.exp (-Real.log 2) := hexp.symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hL1
  · calc Real.exp L ≤ Real.exp (Real.log (Real.sqrt 2 / 2)) :=
        Real.exp_le_exp.mpr hL2
      _ = Real.sqrt 2 / 2 := Real.exp_log (by positivity)
  · have hcomp : Tendsto (fun n : ℕ =>
        Real.exp (Real.log (transferSup n) / n)) atTop (𝓝 (Real.exp L)) :=
      (Real.continuous_exp.tendsto L).comp hLt
    apply hcomp.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.rpow_def_of_pos (transferSup_pos n)]
    congr 1
    field_simp

/-- The bracketed Perron growth root is unique. -/
theorem existsUnique_perron_root :
    ∃! ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ ≤ Real.sqrt 2 / 2 ∧
      Tendsto (fun n : ℕ => (transferSup n) ^ ((1 : ℝ) / n))
        atTop (𝓝 ρ) := by
  obtain ⟨ρ, hρlow, hρhigh, hρlim⟩ := exists_perron_root
  refine ⟨ρ, ⟨hρlow, hρhigh, hρlim⟩, ?_⟩
  intro σ hσ
  exact tendsto_nhds_unique hσ.2.2 hρlim
end Fabius
