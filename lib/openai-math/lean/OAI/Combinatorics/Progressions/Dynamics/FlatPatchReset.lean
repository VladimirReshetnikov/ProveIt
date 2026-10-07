import OAI.Combinatorics.Progressions.Estimates.DependentPatchValue
import OAI.Combinatorics.Progressions.Fourier.AffineTorusDensityIncrement

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

def constantSlots {d : ℕ} (x : Fin d → ℝ) : TriangularSlots d where
  center _ := x
  lower _ _ _ _ := rfl

namespace PatchKernel

variable {d : ℕ} (Φ : PatchKernel d)

noncomputable def periodicValue (x : Fin d → ℝ) : ℝ := (constantSlots x).patchValue Φ

theorem periodicValue_mem_Icc (x : Fin d → ℝ) : Φ.periodicValue x ∈ Set.Icc (0 : ℝ) 1 :=
  (constantSlots x).patchValue_mem_Icc Φ

theorem kernel_le_periodicValue (x : Fin d → ℝ) (b : Fin d → ℤ) :
    Φ.value (fun i => (b i : ℝ) - x i) ≤ Φ.periodicValue x := by
  by_cases hb : Φ.value (fun i => (b i : ℝ) - x i) = 0
  · rw [hb]
    exact (Φ.periodicValue_mem_Icc x).1
  · exact le_of_eq ((constantSlots x).patchValue_eq_of_nonzero Φ hb).symm

theorem periodicValue_sub_le (x y : Fin d → ℝ) :
    Φ.periodicValue x - Φ.periodicValue y ≤ Φ.lip * dist x y := by
  by_cases hx : ∃ b : Fin d → ℤ, Φ.value (fun i => (b i : ℝ) - x i) ≠ 0
  · obtain ⟨b, hb⟩ := hx
    have heq := (constantSlots x).patchValue_eq_of_nonzero Φ hb
    have hle := Φ.kernel_le_periodicValue y b
    have hdist := Φ.lipschitz.dist_le_mul
      ((fun i => (b i : ℝ)) - x) ((fun i => (b i : ℝ)) - y)
    rw [dist_sub_left, Real.dist_eq] at hdist
    have habs := (le_abs_self
      (Φ.value (fun i => (b i : ℝ) - x i) - Φ.value (fun i => (b i : ℝ) - y i))).trans hdist
    change Φ.periodicValue x = Φ.value (fun i => (b i : ℝ) - x i) at heq
    linarith
  · have hz : Φ.periodicValue x = 0 := by
      apply (constantSlots x).patchValue_eq_zero Φ
      intro b
      exact not_ne_iff.mp (fun hb => hx ⟨b, hb⟩)
    have hy := (Φ.periodicValue_mem_Icc y).1
    have hnonneg : 0 ≤ (Φ.lip : ℝ) * dist x y := mul_nonneg Φ.lip.coe_nonneg dist_nonneg
    linarith

theorem periodicValue_lipschitz : LipschitzWith Φ.lip Φ.periodicValue := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  have hxy := Φ.periodicValue_sub_le x y
  have hyx := Φ.periodicValue_sub_le y x
  rw [dist_comm y x] at hyx
  constructor <;> linarith

theorem periodicValue_integer_periodic (x : Fin d → ℝ) (m : Fin d → ℤ) :
    Φ.periodicValue (fun i => x i + m i) = Φ.periodicValue x := by
  change (∑' b : Fin d → ℤ, Φ.value (fun i => (b i : ℝ) - (x i + m i))) =
    ∑' b : Fin d → ℤ, Φ.value (fun i => (b i : ℝ) - x i)
  have heq := (Equiv.addRight m).tsum_eq
    (fun b : Fin d → ℤ => Φ.value (fun i => (b i : ℝ) - (x i + m i)))
  refine heq.symm.trans (tsum_congr fun b => ?_)
  congr 1
  funext i
  change ((b i + m i : ℤ) : ℝ) - (x i + m i) = (b i : ℝ) - x i
  push_cast
  ring

theorem affine_density_increment {N H : ℕ} (hH : 0 < H)
    (hsize : H ^ (2 * d + 1) ≤ N) (alpha beta : Fin d → ℝ) (f : ℕ → ℝ)
    (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b σ : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ)
    (hsmall : 4 * (Φ.lip : ℝ) ≤ σ * H)
    (hscore : σ ≤ 𝔼 n : Fin N,
      (f n.val - b) * Φ.periodicValue (fun i => (n.val : ℝ) * alpha i + beta i)) :
    ∃ q a len : ℕ, 0 < q ∧ q ≤ H ^ (2 * d) ∧
      σ * H / 4 ≤ len ∧ len ≤ H ∧ (∀ j < len, a + q * j < N) ∧
      b < 𝔼 j : Fin len, f (a + q * j.val) := by
  simpa only [Fintype.card_fin] using affine_torus_density_increment hH
    (by simpa only [Fintype.card_fin] using hsize) alpha beta f
    Φ.periodicValue_lipschitz Φ.periodicValue_integer_periodic Φ.periodicValue_mem_Icc
    hf hb hσ hsmall hscore

end PatchKernel
end Erdos3

end

end OAI
