import OAI.Combinatorics.Progressions.Estimates.DependentPatchValue

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_mul_unit_interval {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {L M : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    (hfI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hgI : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    LipschitzWith (L + M) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h₁ : dist (f x * g x) (f y * g x) ≤ dist (f x) (f y) := by
    rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg (hgI x).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (hgI x).2
  have h₂ : dist (f y * g x) (f y * g y) ≤ dist (g x) (g y) := by
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (hfI y).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hfI y).2
  exact (dist_triangle _ (f y * g x) _).trans
    ((add_le_add (h₁.trans (hf.dist_le_mul _ _)) (h₂.trans (hg.dist_le_mul _ _))).trans_eq
      (by simp [add_mul]))

namespace PatchKernel

variable {d : ℕ}

def weight (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : PatchKernel d where
  value x := Φ.value x * f x
  nonneg x := mul_nonneg (Φ.nonneg x) (hI x).1
  le_one x := (mul_le_of_le_one_left (hI x).1 (Φ.le_one x)).trans (hI x).2
  support x hx := Φ.support x (mul_ne_zero_iff.mp hx).1
  lip := Φ.lip + L
  lipschitz := lipschitz_mul_unit_interval Φ.lipschitz hf (fun x => ⟨Φ.nonneg x, Φ.le_one x⟩) hI

@[simp] theorem weight_lip (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (Φ.weight f L hf hI).lip = Φ.lip + L := rfl

@[simp] theorem weight_value (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (x : Fin d → ℝ) :
    (Φ.weight f L hf hI).value x = Φ.value x * f x := rfl

def weightAlong {m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (g : (Fin d → ℝ) → Fin m → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g) : PatchKernel d :=
  Φ.weight (fun x => Ψ.value (g x)) (Ψ.lip * K) (Ψ.lipschitz.comp hg)
    (fun x => ⟨Ψ.nonneg (g x), Ψ.le_one (g x)⟩)

@[simp] theorem weightAlong_lip {m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (g : (Fin d → ℝ) → Fin m → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g) :
    (Φ.weightAlong Ψ g K hg).lip = Φ.lip + Ψ.lip * K := rfl

@[simp] theorem weightAlong_value {m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (g : (Fin d → ℝ) → Fin m → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g)
    (x : Fin d → ℝ) : (Φ.weightAlong Ψ g K hg).value x = Φ.value x * Ψ.value (g x) := rfl

end PatchKernel
end Erdos3

end

end OAI
