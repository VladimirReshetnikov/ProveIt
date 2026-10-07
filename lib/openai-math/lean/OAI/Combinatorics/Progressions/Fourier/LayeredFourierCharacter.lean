/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.SubspaceLayeredModeSmoothRemoval

namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

noncomputable def layeredCoefficientCharacter {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) : ℂ :=
  character (((∑ j, L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j))) : ℝ) :
    CircleFourier.Circle)

noncomputable def layeredSiteWeight {I K S : Type*} [Fintype K] [Fintype S]
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) : ℂ :=
  character ((MvPolynomial.eval (fun z => b z.1 z.2) Q : ℝ) : CircleFourier.Circle) *
    ∏ s, test s (integerSiteValue (site s) b)

theorem layeredCoefficientCharacter_norm {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) :
    ‖layeredCoefficientCharacter L p b‖ = 1 := norm_character _

theorem layeredSiteWeight_norm_le {I K S : Type*} [Fintype K] [Fintype S]
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) (b : K → I → ℝ) :
    ‖layeredSiteWeight Q site test b‖ ≤ 1 := by
  rw [layeredSiteWeight, norm_mul, norm_character, one_mul, norm_prod]
  exact Finset.prod_le_one₀ (fun s _ => norm_nonneg _) (fun s _ => htest s _)

theorem layeredModeTestedPhase_eq_weight_mul {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    layeredModeTestedPhase L p Q site test b =
      layeredSiteWeight Q site test b * layeredCoefficientCharacter L p b := by
  unfold layeredModeTestedPhase layeredSiteWeight layeredCoefficientCharacter
  rw [AddCircle.coe_add, character_add]
  ring

end Erdos3.VectorPolynomial

end

end OAI
