import OAI.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem latticeGaussianMass_ge_multiples (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (ξ : E) (hξΛ : ξ ∈ Λ) (hξ : ξ ≠ 0) (M : ℕ) (hM : (M : ℝ) * ‖ξ‖ ≤ 1) :
    ((M : ℝ) + 1) * Real.exp (-Real.pi) ≤ latticeGaussianMass Λ 1 0 := by
  classical
  let v : ℕ → Λ := fun n => n • (⟨ξ, hξΛ⟩ : Λ)
  have hv (n : ℕ) : (v n : E) = (n : ℝ) • ξ := by
    rw [Nat.cast_smul_eq_nsmul]
    exact map_nsmul Λ.subtype n ⟨ξ, hξΛ⟩
  have hinj : Function.Injective v := by
    intro n m h
    have he := congrArg (fun x : Λ => (x : E)) h
    rw [hv, hv] at he
    exact Nat.cast_injective (smul_left_injective ℝ hξ he)
  have hterm (n : ℕ) (hn : n ∈ Finset.range (M + 1)) :
      Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * 1 * ‖(0 : E) - (v n : E)‖ ^ 2) := by
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hnorm : ‖(0 : E) - (v n : E)‖ ≤ 1 := by
      rw [zero_sub, norm_neg, hv, norm_smul, Real.norm_natCast]
      exact (mul_le_mul_of_nonneg_right hnM (norm_nonneg ξ)).trans hM
    apply Real.exp_le_exp.mpr
    have hsq : ‖(0 : E) - (v n : E)‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) hnorm
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsq)]
  have hsum := Finset.sum_le_sum hterm
  have hbound := (lattice_gaussian_summable Λ (show (0 : ℝ) < 1 by norm_num) 0).sum_le_tsum
    ((Finset.range (M + 1)).image v) (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)] at hbound
  have hcount : (∑ _n ∈ Finset.range (M + 1), Real.exp (-Real.pi)) =
      ((M : ℝ) + 1) * Real.exp (-Real.pi) := by simp
  rw [hcount] at hsum
  exact hsum.trans hbound

theorem latticeGaussianMass_mul_norm_ge (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (ξ : E) (hξΛ : ξ ∈ Λ) (hξ : ξ ≠ 0) :
    Real.exp (-Real.pi) ≤ ‖ξ‖ * latticeGaussianMass Λ 1 0 := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let M := ⌊‖ξ‖⁻¹⌋₊
  have hM : (M : ℝ) * ‖ξ‖ ≤ 1 := by
    calc
      _ ≤ ‖ξ‖⁻¹ * ‖ξ‖ := mul_le_mul_of_nonneg_right (Nat.floor_le (inv_nonneg.mpr hn.le)) hn.le
      _ = 1 := inv_mul_cancel₀ hn.ne'
  have hmass := latticeGaussianMass_ge_multiples Λ ξ hξΛ hξ M hM
  have hlarge : 1 ≤ ‖ξ‖ * ((M : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one ‖ξ‖⁻¹).le hn.le
    rw [mul_inv_cancel₀ hn.ne'] at h
    exact h
  calc
    _ ≤ (‖ξ‖ * ((M : ℝ) + 1)) * Real.exp (-Real.pi) :=
      le_mul_of_one_le_left (Real.exp_pos _).le hlarge
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hmass hn.le]

theorem latticeGaussianMass_controls_integer_factor (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (ξ ζ : E) (hζΛ : ζ ∈ Λ) (hζ : ζ ≠ 0) (m : ℤ) (hξ : ξ = (m : ℝ) • ζ) :
    |(m : ℝ)| ≤ Real.exp Real.pi * ‖ξ‖ * latticeGaussianMass Λ 1 0 := by
  have hnorm : ‖ξ‖ = |(m : ℝ)| * ‖ζ‖ := by rw [hξ, norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left (latticeGaussianMass_mul_norm_ge Λ ζ hζΛ hζ)
    (abs_nonneg (m : ℝ))
  have hexp : Real.exp Real.pi * Real.exp (-Real.pi) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos Real.pi).le
  have hl : Real.exp Real.pi * (|(m : ℝ)| * Real.exp (-Real.pi)) = |(m : ℝ)| := by
    calc
      _ = |(m : ℝ)| * (Real.exp Real.pi * Real.exp (-Real.pi)) := by ring
      _ = _ := by rw [hexp, mul_one]
  rw [hl] at hh
  rw [hnorm]
  simpa only [mul_assoc] using hh

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem latticeGaussianMass_ge_multiples_at_temperature
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (ξ : E) (hξΛ : ξ ∈ Λ) (hξ : ξ ≠ 0)
    {t : ℝ} (ht : 0 < t) (M : ℕ) (hM : (M : ℝ) * (Real.sqrt t * ‖ξ‖) ≤ 1) :
    ((M : ℝ) + 1) * Real.exp (-Real.pi) ≤ latticeGaussianMass Λ t 0 := by
  classical
  let v : ℕ → Λ := fun n => n • (⟨ξ, hξΛ⟩ : Λ)
  have hv (n : ℕ) : (v n : E) = (n : ℝ) • ξ := by
    rw [Nat.cast_smul_eq_nsmul]
    exact map_nsmul Λ.subtype n ⟨ξ, hξΛ⟩
  have hinj : Function.Injective v := by
    intro n m h
    have he := congrArg (fun x : Λ => (x : E)) h
    rw [hv, hv] at he
    exact Nat.cast_injective (smul_left_injective ℝ hξ he)
  have hterm (n : ℕ) (hn : n ∈ Finset.range (M + 1)) :
      Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * t * ‖(0 : E) - (v n : E)‖ ^ 2) := by
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hnorm : Real.sqrt t * ‖(0 : E) - (v n : E)‖ ≤ 1 := by
      rw [zero_sub, norm_neg, hv, norm_smul, Real.norm_natCast]
      calc
        _ = (n : ℝ) * (Real.sqrt t * ‖ξ‖) := by ring
        _ ≤ (M : ℝ) * (Real.sqrt t * ‖ξ‖) :=
          mul_le_mul_of_nonneg_right hnM (by positivity)
        _ ≤ 1 := hM
    have hsq := pow_le_one₀ (by positivity : 0 ≤ Real.sqrt t * ‖(0 : E) - (v n : E)‖) hnorm (n := 2)
    rw [mul_pow, Real.sq_sqrt ht.le] at hsq
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsq)]
  have hsum := Finset.sum_le_sum hterm
  have hbound := (lattice_gaussian_summable Λ ht 0).sum_le_tsum
    ((Finset.range (M + 1)).image v) (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)] at hbound
  have hcount : (∑ _n ∈ Finset.range (M + 1), Real.exp (-Real.pi)) =
      ((M : ℝ) + 1) * Real.exp (-Real.pi) := by simp
  rw [hcount] at hsum
  exact hsum.trans hbound

theorem latticeGaussianMass_mul_scaled_norm_ge
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (ξ : E) (hξΛ : ξ ∈ Λ) (hξ : ξ ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    Real.exp (-Real.pi) ≤ (Real.sqrt t * ‖ξ‖) * latticeGaussianMass Λ t 0 := by
  have hn : 0 < Real.sqrt t * ‖ξ‖ := mul_pos (Real.sqrt_pos.mpr ht) (norm_pos_iff.mpr hξ)
  let M := ⌊(Real.sqrt t * ‖ξ‖)⁻¹⌋₊
  have hM : (M : ℝ) * (Real.sqrt t * ‖ξ‖) ≤ 1 := by
    calc
      _ ≤ (Real.sqrt t * ‖ξ‖)⁻¹ * (Real.sqrt t * ‖ξ‖) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (inv_nonneg.mpr hn.le)) hn.le
      _ = 1 := inv_mul_cancel₀ hn.ne'
  have hmass := latticeGaussianMass_ge_multiples_at_temperature Λ ξ hξΛ hξ ht M hM
  have hlarge : 1 ≤ (Real.sqrt t * ‖ξ‖) * ((M : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one (Real.sqrt t * ‖ξ‖)⁻¹).le hn.le
    rw [mul_inv_cancel₀ hn.ne'] at h
    exact h
  calc
    _ ≤ ((Real.sqrt t * ‖ξ‖) * ((M : ℝ) + 1)) * Real.exp (-Real.pi) :=
      le_mul_of_one_le_left (Real.exp_pos _).le hlarge
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hmass hn.le]

end Erdos3

end

end OAI
