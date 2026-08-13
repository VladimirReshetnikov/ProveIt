/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationCertificateData

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

/-- One breadth step using the standard rotation and a second generator. -/
def generationStep (g : S5) (stage : Finset S5) : Finset S5 :=
  stage ∪ stage.image (fun x ↦ fiveCycle * x) ∪
    stage.image (fun x ↦ fiveCycle⁻¹ * x) ∪
    stage.image (fun x ↦ g * x) ∪
    stage.image (fun x ↦ g⁻¹ * x)

def iterateGenerationStep (g : S5) (seed : Finset S5) : ℕ → Finset S5
  | 0 => seed
  | n + 1 => generationStep g (iterateGenerationStep g seed n)

def generatedStage (g : S5) (n : ℕ) : Finset S5 :=
  iterateGenerationStep g {1} n

theorem iterateGenerationStep_add (g : S5) (seed : Finset S5) (m n : ℕ) :
    iterateGenerationStep g seed (m + n) =
      iterateGenerationStep g (iterateGenerationStep g seed m) n := by
  induction n with
  | zero => simp [iterateGenerationStep]
  | succ n ih =>
      rw [Nat.add_succ, iterateGenerationStep, iterateGenerationStep, ih]

theorem generatedStage_add (g : S5) (m n : ℕ) :
    generatedStage g (m + n) =
      iterateGenerationStep g (generatedStage g m) n := by
  simpa only [generatedStage] using
    iterateGenerationStep_add g ({1} : Finset S5) m n

theorem generationStep_subset_subgroup
    (H : Subgroup S5) (g : S5)
    (hfive : fiveCycle ∈ H) (hg : g ∈ H)
    (stage : Finset S5) (hstage : ∀ x ∈ stage, x ∈ H) :
    ∀ x ∈ generationStep g stage, x ∈ H := by
  intro x hx
  simp only [generationStep, Finset.mem_union] at hx
  rcases hx with ((((hx | hx) | hx) | hx) | hx)
  · exact hstage x hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact H.mul_mem hfive (hstage y hy)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact H.mul_mem (H.inv_mem hfive) (hstage y hy)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact H.mul_mem hg (hstage y hy)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact H.mul_mem (H.inv_mem hg) (hstage y hy)

theorem iterateGenerationStep_subset_subgroup
    (H : Subgroup S5) (g : S5)
    (hfive : fiveCycle ∈ H) (hg : g ∈ H)
    (seed : Finset S5) (hseed : ∀ x ∈ seed, x ∈ H) :
    ∀ n x, x ∈ iterateGenerationStep g seed n → x ∈ H := by
  intro n
  induction n with
  | zero =>
      intro x hx
      exact hseed x hx
  | succ n ih =>
      exact generationStep_subset_subgroup H g hfive hg
        (iterateGenerationStep g seed n) ih

theorem generatedStage_subset_subgroup
    (H : Subgroup S5) (g : S5)
    (hfive : fiveCycle ∈ H) (hg : g ∈ H) :
    ∀ n x, x ∈ generatedStage g n → x ∈ H := by
  intro n x hx
  apply iterateGenerationStep_subset_subgroup H g hfive hg
    ({1} : Finset S5) (by
      intro y hy
      have hy' : y = 1 := by simpa using hy
      subst y
      exact H.one_mem) n x
  exact hx

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates
