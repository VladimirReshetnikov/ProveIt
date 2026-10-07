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
  let x := (N : Real) / (2 * R)
  let c := Nat.ceil x
  have hx2 : 2 ≤ x := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hc : x ≤ c := Nat.le_ceil _
  have hc2 : 2 ≤ c := by exact_mod_cast hx2.trans hc
  have hcup : (c : Real) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  let M := 2 * (c - 1)
  have hMcast : (M : Real) = 2 * ((c : Real) - 1) := by
    simp only [M, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one]
  have hMlo : x ≤ (M : Real) := by rw [hMcast]; linarith
  have hMhi : (M : Real) < (N : Real) / R := by
    have heq : (N : Real) / R = 2 * x := by dsimp [x]; ring
    rw [heq, hMcast]
    linarith
  have hM0 : 0 < M := by dsimp [M]; omega
  refine ⟨M, hM0, ⟨c - 1, by dsimp [M]; omega⟩, ?_, hMlo, hMhi⟩
  have hprod := (lt_div_iff₀ hR0).mp hMhi
  have h2 : (2 : Real) * M ≤ N := by
    have hm := mul_le_mul_of_nonneg_left hR2 (show (0 : Real) ≤ M by positivity)
    nlinarith
  exact_mod_cast h2

theorem recurrence_fourier_frequency_bound {N R M : Nat}
    (hR : 0 < R) (hM : 0 < M) (hscale : (N : Real) / (2 * R) ≤ M) :
    (N : Real) ^ 2 / (M : Real) ^ 2 ≤ 4 * (R : Real) ^ 2 := by
  have hRr : (0 : Real) < R := by exact_mod_cast hR
  have hMr : (0 : Real) < M := by exact_mod_cast hM
  have h := (div_le_iff₀ (show (0 : Real) < 2 * R by positivity)).mp hscale
  have hp := pow_le_pow_left₀ (show (0 : Real) ≤ N by positivity) h 2
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [hp]

theorem recurrence_fourier_norm_lower {N R M t : Nat}
    (hN : 0 < N) (hR : 0 < R) (hscale : (N : Real) / (2 * R) ≤ M) :
    (t : Real) / (8 * R) ≤ (t : Real) * M / (4 * N) := by
  have hNr : (0 : Real) < N := by exact_mod_cast hN
  have hRr : (0 : Real) < R := by exact_mod_cast hR
  calc
    _ = (t : Real) * ((N : Real) / (2 * R)) / (4 * N) := by field_simp; ring
    _ ≤ _ := by gcongr

end LeanProofs.GowersSzemeredi
