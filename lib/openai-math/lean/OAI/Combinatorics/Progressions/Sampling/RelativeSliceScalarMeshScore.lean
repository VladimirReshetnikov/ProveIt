import OAI.Combinatorics.Progressions.Estimates.RelativeScalarPassageDiscount
import OAI.Combinatorics.Progressions.Estimates.UnconditionedTrimmedSliceFamily

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {J X : Type*} [Fintype J] [decJ : DecidableEq J] [Fintype X]
variable {N : J → ℕ} {q r s d : ℕ}

theorem relativeSlice_scalar_mesh_score
    (original : ResidueBoxSlice N q) (hOriginal : ∀ j, 0 < original.length j)
    (mesh : ResidueBoxSlice N r) (hMesh : ∀ j, 0 < mesh.length j)
    (P : PolynomialPatch X s d) (f : (X → ℤ) → ℝ)
    (parent : X → ℤ) (H : X → ℕ) (frame : Option J × X → ℤ)
    (hinside : ∀ u : integerBox N,
      smoothAffineSample u.val frame ∈ translatedIntegerBox parent H)
    (hf : ∀ x ∈ translatedIntegerBox parent H, f x ∈ Set.Icc (0 : ℝ) 1)
    {τ Λ δ η : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hΛ : Λ ∈ Set.Icc (0 : ℝ) 1)
    (hscore : δ ≤ (original.fullSliceLaw hOriginal).mean (fun u =>
      (f (smoothAffineSample u.val frame) - Λ) *
        P.value (fun i => (smoothAffineSample u.val frame i : ℝ))))
    (happrox : ∀ test : integerBox N → ℝ, (∀ u, |test u| ≤ 1) →
      |(original.fullSliceLaw hOriginal).mean test - (mesh.fullSliceLaw hMesh).mean test| ≤ η) :
    δ - η ≤ rectangularScalarDiscrepancy parent H
      (fun x => ((f x * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ))
      (fun x => (P.value (fun i => (x i : ℝ)) : ℂ))
      (relativeScalarPassageSlack τ) ((1 - τ) * Λ) r
      (fun j => (mesh.start j : ℤ)) 0 (fun j => (mesh.length j : ℤ))
      (fun j => by change (0 : ℤ) < (mesh.length j : ℤ); exact_mod_cast hMesh j) frame := by
  have hdec : decJ = Classical.decEq J := Subsingleton.elim _ _
  subst decJ
  rw [mesh.rectangularScalarDiscrepancy_eq_fullSliceLaw hMesh parent H _ _ _ _ frame hinside]
  simp only [Complex.ofReal_re]
  apply relativeScalarPassage_mesh_score (original.fullSliceLaw hOriginal)
    (mesh.fullSliceLaw hMesh) (fun u => f (smoothAffineSample u.val frame))
    (fun u => P.value (fun i => (smoothAffineSample u.val frame i : ℝ)))
    hτ hτhalf hΛ.1 (fun u => (P.value_mem_Icc _).1) hscore
  apply happrox
  intro u
  have hf' := hf _ (hinside u)
  have hg := P.value_mem_Icc (fun i => (smoothAffineSample u.val frame i : ℝ))
  have hdiff : |f (smoothAffineSample u.val frame) - Λ| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hf'.1, hΛ.2], by linarith [hf'.2, hΛ.1]⟩
  rw [abs_mul, abs_of_nonneg hg.1]
  exact (mul_le_mul_of_nonneg_right hdiff hg.1).trans (by simpa using hg.2)

end Erdos3

end

end OAI
