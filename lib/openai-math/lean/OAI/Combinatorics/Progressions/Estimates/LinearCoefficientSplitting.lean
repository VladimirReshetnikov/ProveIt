import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity

namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

theorem exists_biased_linear_coefficient_splitting
    {σ ι V : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (hη : η ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] V)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (e p r : σ → ℝ ⊗[ℚ] V),
      0 < m ∧ m ≤ H ∧
      (∀ i, e i + p i + r i = a i) ∧
      (∀ i, realifyFunctional η (p i) = 0) ∧
      (∀ i j, |(b.baseChange ℝ).repr (e i) j| ≤ (H : ℝ) / (2 * T i * δ)) ∧
      (fun z : σ × ι => (b.baseChange ℝ).repr (r z.1) z.2) ∈ realDenominatorGrid m := by
  classical
  obtain ⟨v, m, hm, hmH, hv, hvheight, z, hz⟩ := exists_bounded_frequency_direction b η hη hH hheight
  let vR : ℝ ⊗[ℚ] V := (1 : ℝ) ⊗ₜ[ℚ] v
  let c : σ → ℝ := fun i => realifyFunctional η (a i)
  let n : σ → ℤ := fun i => round (c i)
  let e := fun i => (c i - (n i : ℝ)) • vR
  let p := fun i => a i - c i • vR
  let r := fun i => (n i : ℝ) • vR
  have hvR : realifyFunctional η vR = 1 := by simp only [vR, realifyFunctional_tmul, hv, Rat.cast_one, one_mul]
  have hcoord (j : ι) : (b.baseChange ℝ).repr vR j = (b.repr v j : ℝ) := by
    simp only [vR, Basis.baseChange_repr_tmul, Rat.smul_def, mul_one]
  have hnear : ∀ i, |c i - (n i : ℝ)| ≤ 1 / (2 * T i * δ) :=
    linear_phase_near_integers T hT c hδ hbias
  refine ⟨m, e, p, r, hm, hmH, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [e, p, r]
    rw [sub_smul]
    abel
  · intro i
    simp only [p, map_sub, map_smul, hvR, smul_eq_mul, mul_one, c, sub_self]
  · intro i j
    change |(b.baseChange ℝ).repr ((c i - (n i : ℝ)) • vR) j| ≤ _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, hcoord]
    calc
      _ ≤ |c i - (n i : ℝ)| * H :=
        mul_le_mul_of_nonneg_left (hvheight j).abs_real_le (abs_nonneg _)
      _ ≤ (1 / (2 * T i * δ)) * H := mul_le_mul_of_nonneg_right (hnear i) (Nat.cast_nonneg H)
      _ = _ := by ring
  · refine ⟨fun ij => n ij.1 * z ij.2, ?_⟩
    funext ij
    change ((n ij.1 * z ij.2 : ℤ) : ℝ) = (m : ℝ) * (b.baseChange ℝ).repr ((n ij.1 : ℝ) • vR) ij.2
    rw [Int.cast_mul, map_smul, Finsupp.smul_apply, smul_eq_mul, hcoord]
    have hz' : (m : ℝ) * (b.repr v ij.2 : ℝ) = (z ij.2 : ℝ) := by exact_mod_cast hz ij.2
    calc
      (n ij.1 : ℝ) * (z ij.2 : ℝ) = (n ij.1 : ℝ) * ((m : ℝ) * (b.repr v ij.2 : ℝ)) := by rw [hz']
      _ = _ := by ring

end Erdos3

end

end OAI
