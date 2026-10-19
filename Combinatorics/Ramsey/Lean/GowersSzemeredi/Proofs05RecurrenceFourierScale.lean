import GowersSzemeredi.Section05

/-! A rounding-safe Fourier detection interval. Its radius is strictly
below `N/R`, so exclusion of strict recurrence suffices, including when
the ratio is an integer. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem recurrence_fourier_interval_scale {N R : Nat} (hR : 2 ≤ R) (hN : 4 * R ≤ N) :
    ∃ M : Nat, 0 < M ∧ Even M ∧ 2 * M ≤ N ∧
      (N : Real) / (2 * R) ≤ M ∧ (M : Real) < (N : Real) / R := by
  have hR0 : (0 : Real) < R := by exact_mod_cast (show 0 < R by omega)
  have hR2 : (2 : Real) ≤ R := by exact_mod_cast hR
  have hNr : 4 * (R : Real) ≤ N := by exact_mod_cast hN
  -- `M = 2 ⌈y⌉` with `y = N / (4 R) ≥ 1`, so `2 y ≤ M < 2 y + 2 ≤ 4 y`
  let y := (N : Real) / (4 * R)
  have hy : 1 ≤ y := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hc : y ≤ ⌈y⌉₊ := Nat.le_ceil _
  have hcup : (⌈y⌉₊ : Real) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  have hMlo : (N : Real) / (2 * R) ≤ (2 * ⌈y⌉₊ : Nat) := by
    rw [show (N : Real) / (2 * R) = 2 * y by dsimp only [y]; ring]; push_cast; linarith
  have hMhi : ((2 * ⌈y⌉₊ : Nat) : Real) < N / R := by
    rw [show (N : Real) / R = 4 * y by dsimp only [y]; ring]; push_cast; linarith
  have h2 : (2 : Real) * (2 * ⌈y⌉₊ : Nat) ≤ N := by
    linarith [(lt_div_iff₀ hR0).mp hMhi,
      mul_le_mul_of_nonneg_left hR2 (Nat.cast_nonneg (α := Real) (2 * ⌈y⌉₊))]
  refine ⟨2 * ⌈y⌉₊, ?_, ⟨_, two_mul _⟩, by exact_mod_cast h2, hMlo, hMhi⟩
  have := Nat.one_le_cast.mp (hy.trans hc)
  omega

theorem recurrence_fourier_frequency_bound {N R M : Nat}
    (hR : 0 < R) (hM : 0 < M) (hscale : (N : Real) / (2 * R) ≤ M) :
    (N : Real) ^ 2 / (M : Real) ^ 2 ≤ 4 * (R : Real) ^ 2 := by
  have h := (div_le_iff₀ (show (0 : Real) < 2 * R by positivity)).mp hscale
  have hp := pow_le_pow_left₀ (show (0 : Real) ≤ N by positivity) h 2
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [hp]

theorem recurrence_fourier_norm_lower {N R M t : Nat}
    (hN : 0 < N) (hR : 0 < R) (hscale : (N : Real) / (2 * R) ≤ M) :
    (t : Real) / (8 * R) ≤ (t : Real) * M / (4 * N) := by
  calc
    _ = (t : Real) * ((N : Real) / (2 * R)) / (4 * N) := by field_simp; ring
    _ ≤ _ := by gcongr

end LeanProofs.GowersSzemeredi
