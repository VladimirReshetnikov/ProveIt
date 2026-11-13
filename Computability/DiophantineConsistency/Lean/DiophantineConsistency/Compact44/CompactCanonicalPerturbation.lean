import DiophantineConsistency.Compact44.ChosenControllerCalibration
import DiophantineConsistency.Compact44.CompactRankVariationRetry

/-! Bounded attempt: construct the modified word explicitly; its full
PackingInput preservation remains an explicit, unproved premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactCanonicalPerturbation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticPackingBlocks
open DiophantineConsistency.ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactChosenControllerCalibration CompactRankVariation
attribute [local irreducible] paramKernel rho

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def perturb (X0 δ : V → V) (j : V) : V := X0 j + Exp.exp (67*1063) * δ j

instance perturb_definable (X0 δ : V → V) [𝚺₁-Function₁ X0] [𝚺₁-Function₁ δ] :
    𝚺₁-Function₁ (perturb X0 δ) := by
  unfold perturb
  definability

theorem chosen_rank_if_stable (T MC HP c : V) {X0 : V → V} [𝚺₁-Function₁ X0]
    (h0 : PackingInput 590069 (paramKernel rho : V) MC HP
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) X0)
    (hstable : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) →
      PackingInput 590069 (paramKernel rho : V) MC HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb X0 δ)) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) ∧
      PackingInput 590069 (paramKernel rho : V) MC HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb X0 δ) ∧
      windowRank (paramKernel rho : V) (power 581197 ((2*T+3)+1))
        (power 581197 (T+1)) c (perturb X0 δ) % (590069 * power 581197 ((2*T+3)+1)) =
          (590069 * power 581197 (T+1)) % (590069 * power 581197 ((2*T+3)+1)) := by
  obtain ⟨δ, hδd, hδb, hδs, hcal⟩ := chosen_calibration T
    (windowRank (paramKernel rho : V) (power 581197 ((2*T+3)+1))
      (power 581197 (T+1)) c X0)
  letI : 𝚺₁-Function₁ δ := hδd
  have h1 := hstable δ hδd hδb hδs
  have hX : ∀ j < power 581197 ((2*T+3)+1),
      perturb X0 δ j = X0 j + Exp.exp (67*1063) * δ j := by
    intro j _
    rfl
  have hs : ∀ j, δ j ≠ 0 → j+1 < power 581197 ((2*T+3)+1) ∧
      j+power 581197 (T+1) < power 581197 ((2*T+3)+1) :=
    fun j hj => ⟨(hδs j hj).2.1, (hδs j hj).2.2⟩
  exact ⟨δ, hδd, hδb, hδs, h1, calibrated_rank h0 h1 hX hδb hs hcal⟩

#print axioms perturb_definable
#print axioms chosen_rank_if_stable
end CompactCanonicalPerturbation
