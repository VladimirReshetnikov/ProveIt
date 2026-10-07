import OAI.Combinatorics.Progressions.Dynamics.FlatPatchReset
import OAI.Combinatorics.Progressions.Estimates.NormalizedCutoffs

namespace OAI

section

namespace Erdos3.PatchKernel

open scoped NNReal

variable {d : ℕ} {ι : Type*} [Fintype ι]

noncomputable def translateSum (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (x : Fin d → ℝ) : ℝ := ∑ i, Φ.periodicValue (x - c i)

theorem translateSum_nonneg (Φ : PatchKernel d) (c : ι → Fin d → ℝ) (x : Fin d → ℝ) :
    0 ≤ Φ.translateSum c x := Finset.sum_nonneg (fun i _ => (Φ.periodicValue_mem_Icc (x - c i)).1)

theorem periodicValue_le_translateSum (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (i : ι) (x : Fin d → ℝ) : Φ.periodicValue (x - c i) ≤ Φ.translateSum c x := by
  exact Finset.single_le_sum (f := fun j => Φ.periodicValue (x - c j))
    (fun j _ => (Φ.periodicValue_mem_Icc (x - c j)).1) (Finset.mem_univ i)

theorem abs_translateSum_sub_le (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (x y : Fin d → ℝ) :
    |Φ.translateSum c x - Φ.translateSum c y| ≤ Fintype.card ι * Φ.lip * dist x y := by
  unfold translateSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |Φ.periodicValue (x - c i) - Φ.periodicValue (y - c i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (Φ.lip : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.dist_eq, dist_sub_right] using Φ.periodicValue_lipschitz.dist_le_mul
        (x - c i) (y - c i)
    _ = _ := by simp [mul_assoc]

theorem translateSum_integer_periodic (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (x : Fin d → ℝ) (m : Fin d → ℤ) :
    Φ.translateSum c (fun j => x j + m j) = Φ.translateSum c x := by
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun j => x j + (m j : ℝ)) - c i = fun j => (x - c i) j + m j := by
    funext j
    simp only [Pi.sub_apply]
    ring
  rw [heq, Φ.periodicValue_integer_periodic]

theorem kernel_le_translateSum (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (i : ι) (x : Fin d → ℝ) : Φ.value x ≤ Φ.translateSum c (c i - x) := by
  have hk := Φ.kernel_le_periodicValue (-x) 0
  have hs := Φ.periodicValue_le_translateSum c i (c i - x)
  have heq : c i - x - c i = -x := by abel
  rw [heq] at hs
  simpa only [Pi.zero_apply, Int.cast_zero, Pi.neg_apply, zero_sub, neg_neg] using hk.trans hs

noncomputable def normalizedTranslate (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hcover : ∀ x, (δ : ℝ) ≤ Φ.translateSum c x) (i : ι) :
    PatchKernel d where
  value x := Φ.value x / Φ.translateSum c (c i - x)
  nonneg x := div_nonneg (Φ.nonneg x) (Φ.translateSum_nonneg c _)
  le_one x := by
    apply (div_le_one ((show (0 : ℝ) < δ from hδ).trans_le (hcover (c i - x)))).mpr
    exact Φ.kernel_le_translateSum c i x
  support x hx := Φ.support x (fun h => hx (by simp only [h, zero_div]))
  lip := Φ.lip / δ + Fintype.card ι * Φ.lip / (δ * δ)
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hnum := Φ.lipschitz.dist_le_mul x y
    have hden := Φ.abs_translateSum_sub_le c (c i - x) (c i - y)
    rw [dist_sub_left] at hden
    have h := abs_div_sub_div_bound (show (0 : ℝ) < δ from hδ) (hcover _) (hcover _)
      (mul_nonneg Φ.lip.coe_nonneg dist_nonneg) zero_le_one
      (by positivity : 0 ≤ (Fintype.card ι : ℝ) * Φ.lip * dist x y)
      hnum (by rw [abs_of_nonneg (Φ.nonneg _)]; exact Φ.le_one _) hden
    apply h.trans_eq
    push_cast
    ring

theorem normalizedTranslate_periodicValue (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hcover : ∀ x, (δ : ℝ) ≤ Φ.translateSum c x)
    (i : ι) (x : Fin d → ℝ) :
    (Φ.normalizedTranslate c δ hδ hcover i).periodicValue (x - c i) =
      Φ.periodicValue (x - c i) / Φ.translateSum c x := by
  have hden (b : Fin d → ℤ) :
      Φ.translateSum c (c i - fun j => (b j : ℝ) - (x - c i) j) = Φ.translateSum c x := by
    have heq : c i - (fun j => (b j : ℝ) - (x - c i) j) = fun j => x j + ((-b j : ℤ) : ℝ) := by
      funext j
      simp only [Pi.sub_apply, Int.cast_neg]
      ring
    rw [heq, Φ.translateSum_integer_periodic]
  change (∑' b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - (x - c i) j) /
    Φ.translateSum c (c i - fun j => (b j : ℝ) - (x - c i) j)) = _
  simp only [hden]
  exact tsum_div_const

theorem sum_normalizedTranslate_periodicValue (Φ : PatchKernel d) (c : ι → Fin d → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hcover : ∀ x, (δ : ℝ) ≤ Φ.translateSum c x)
    (x : Fin d → ℝ) :
    (∑ i, (Φ.normalizedTranslate c δ hδ hcover i).periodicValue (x - c i)) = 1 := by
  simp only [normalizedTranslate_periodicValue, ← Finset.sum_div]
  exact div_self (ne_of_gt (lt_of_lt_of_le hδ (hcover x)))

end Erdos3.PatchKernel

end

end OAI
