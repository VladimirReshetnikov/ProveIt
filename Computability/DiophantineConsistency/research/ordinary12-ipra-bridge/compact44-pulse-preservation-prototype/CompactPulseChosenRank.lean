import CompactPulsePreservationRetry

/-! Apply the pulse reduction to the chosen compact controller.  Uniform
product/block hypotheses remain explicit for every admissible selector. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPulseChosenRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticBinaryCarry
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticPackingBlocks
open DiophantineConsistency.ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactCanonicalPerturbation CompactPulsePreservationRetry
attribute [local irreducible] paramKernel rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The five unresolved product and normalized-block conditions. -/
structure ProductBlockInput (d K HP N s : V) (X : V → V) : Prop where
  hi_lt : ∀ j < N, K * X j < Exp.exp d * Exp.exp d
  cell_sum : ∀ j < N, X j + blk d K N s X j < Exp.exp d
  blk_pos : 0 < blk d K N s X 0
  high_origin : NoCarry (blk d K N s X 0) (HP - 1)
  high : ∀ j < N, 0 < j → NoCarry (blk d K N s X j) HP

theorem chosen_rank_of_pulse (T MC HP c : V) {X0 : V → V} [𝚺₁-Function₁ X0]
    (h0 : PackingInput 590069 (paramKernel rho : V) MC HP
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) X0)
    (hpulse : ∀ j < power 581197 ((2*T+3)+1), 0 < j →
      NoCarry (X0 j + Exp.exp (67*1063)) MC)
    (hblocks : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) →
      ProductBlockInput 590069 (paramKernel rho : V) HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb X0 δ)) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) ∧
      PackingInput 590069 (paramKernel rho : V) MC HP
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb X0 δ) ∧
      windowRank (paramKernel rho : V) (power 581197 ((2*T+3)+1))
        (power 581197 (T+1)) c (perturb X0 δ) % (590069 * power 581197 ((2*T+3)+1)) =
          (590069 * power 581197 (T+1)) % (590069 * power 581197 ((2*T+3)+1)) := by
  apply chosen_rank_if_stable T MC HP c h0
  intro δ hd hb hs
  have hr := hblocks δ hd hb hs
  exact packing_of_pulse h0 hb (fun j hj => (hs j hj).1) hpulse
    hr.hi_lt hr.cell_sum hr.blk_pos hr.high_origin hr.high

#print axioms CompactPulseChosenRank.chosen_rank_of_pulse
end CompactPulseChosenRank
