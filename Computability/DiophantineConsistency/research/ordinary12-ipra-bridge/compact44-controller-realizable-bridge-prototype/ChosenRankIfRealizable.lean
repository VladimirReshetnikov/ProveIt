import ChosenControllerCalibration
import CompactRankVariationRetry

/-! Uncompiled bridge: the chosen abstract controller realizes a calibrated
packing only under an explicit assumption supplying that physical packing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactChosenRankIfRealizable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticPackingBlocks
open DiophantineConsistency.ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactChosenControllerCalibration CompactRankVariation
attribute [local irreducible] paramKernel rho

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem chosen_rank_if_realizable (T MC HP c : V) {X0 : V → V} [𝚺₁-Function₁ X0]
    (h0 : PackingInput 590069 (paramKernel rho : V) MC HP
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) X0)
    (hrealize : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) →
      ∃ X1 : V → V, (𝚺₁-Function₁ X1) ∧
        PackingInput 590069 (paramKernel rho : V) MC HP
          (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) X1 ∧
        ∀ j < power 581197 ((2*T+3)+1),
          X1 j = X0 j + Exp.exp (67*1063) * δ j) :
    ∃ (δ X1 : V → V), (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) ∧
      (𝚺₁-Function₁ X1) ∧
      PackingInput 590069 (paramKernel rho : V) MC HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) X1 ∧
      (∀ j < power 581197 ((2*T+3)+1), X1 j = X0 j + Exp.exp (67*1063) * δ j) ∧
      windowRank (paramKernel rho : V) (power 581197 ((2*T+3)+1))
        (power 581197 (T+1)) c X1 % (590069 * power 581197 ((2*T+3)+1)) =
          (590069 * power 581197 (T+1)) % (590069 * power 581197 ((2*T+3)+1)) := by
  obtain ⟨δ, hδd, hδb, hδs, hcal⟩ := chosen_calibration T
    (windowRank (paramKernel rho : V) (power 581197 ((2*T+3)+1))
      (power 581197 (T+1)) c X0)
  obtain ⟨X1, hX1d, h1, hX⟩ := hrealize δ hδd hδb hδs
  letI : 𝚺₁-Function₁ δ := hδd
  letI : 𝚺₁-Function₁ X1 := hX1d
  have hs : ∀ j, δ j ≠ 0 → j+1 < power 581197 ((2*T+3)+1) ∧
      j+power 581197 (T+1) < power 581197 ((2*T+3)+1) :=
    fun j hj => ⟨(hδs j hj).2.1, (hδs j hj).2.2⟩
  exact ⟨δ, X1, hδd, hδb, hδs, hX1d, h1, hX,
    calibrated_rank h0 h1 hX hδb hs hcal⟩

#print axioms chosen_rank_if_realizable
end CompactChosenRankIfRealizable
