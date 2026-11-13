import DiophantineConsistency.BFS943.DirectBFSControllerUnit
import DiophantineConsistency.Compact44.CompactCanonicalPerturbation
import DiophantineConsistency.Compact44.CompactHaltDimensions
import DiophantineConsistency.Compact44.ArithmeticControllerChoiceCompact44Triangle
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSGenericChosenRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticPackingBlocks ArithmeticPacking
open ArithmeticConstructionUnitCompact44 ArithmeticControllerChoiceCompact44Triangle
open CompactCanonicalPerturbation CompactRankVariation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem chosen_calibration (K : V) (hK : K % 342946332593 = 264033855341) (T R0 : V) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) ∧
      (Gamma K (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) *
        bsum 590069 δ (power 581197 ((2*T+3)+1)) + 590069 * power 581197 (T+1)) %
          (590069 * power 581197 ((2*T+3)+1)) = R0 % (590069 * power 581197 ((2*T+3)+1)) := by
  have hb := CompactHaltDimensions.controller_bounds T
  obtain ⟨Γi,hΓ⟩ := DirectBFSControllerUnit.bfs_gamma_unit K hK (2*T+3) (T+1)
  exact rank_calibration (2*T+3) (power 581197 (T+1)) R0
    (Gamma K (power 581197 ((2*T+3)+1)) (power 581197 (T+1))) Γi hb.2 hb.1 hΓ

theorem chosen_rank_if_stable (K : V) (hK : K % 342946332593 = 264033855341) (T MC HP c : V) {X0 : V → V} [𝚺₁-Function₁ X0]
    (h0 : PackingInput 590069 K MC HP
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) X0)
    (hstable : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) →
      PackingInput 590069 K MC HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb X0 δ)) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) ∧
      PackingInput 590069 K MC HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb X0 δ) ∧
      windowRank K (power 581197 ((2*T+3)+1))
        (power 581197 (T+1)) c (perturb X0 δ) % (590069 * power 581197 ((2*T+3)+1)) =
          (590069 * power 581197 (T+1)) % (590069 * power 581197 ((2*T+3)+1)) := by
  obtain ⟨δ, hδd, hδb, hδs, hcal⟩ := chosen_calibration K hK T
    (windowRank K (power 581197 ((2*T+3)+1))
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


#print axioms DirectBFSGenericChosenRank.chosen_calibration
#print axioms DirectBFSGenericChosenRank.chosen_rank_if_stable
end DirectBFSGenericChosenRank
