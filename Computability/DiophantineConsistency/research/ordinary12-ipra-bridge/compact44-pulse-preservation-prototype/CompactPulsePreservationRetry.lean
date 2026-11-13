import CompactCanonicalPerturbation

/-! Reduce the packing preservation requirement to one single-pulse low-mask
fact and the product/block conditions for the actual perturbed word. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPulsePreservationRetry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticBinaryCarry
open DiophantineConsistency.ArithmeticPacking
open CompactCanonicalPerturbation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Pointwise reconstruction of packing.  Product and normalized block
conditions are explicitly retained, as is low-mask safety of a single pulse. -/
theorem packing_of_pulse {d K MC HP N s : V} {X0 δ : V → V}
    (h0 : PackingInput d K MC HP N s X0)
    (hbool : ∀ j, δ j ≤ 1)
    (hpos : ∀ j, δ j ≠ 0 → 0 < j)
    (hpulse : ∀ j < N, 0 < j →
      NoCarry (X0 j + Exp.exp (67*1063)) MC)
    (hhi : ∀ j < N, K * perturb X0 δ j < Exp.exp d * Exp.exp d)
    (hcell : ∀ j < N, perturb X0 δ j + blk d K N s (perturb X0 δ) j < Exp.exp d)
    (hblk : 0 < blk d K N s (perturb X0 δ) 0)
    (hhigh0 : NoCarry (blk d K N s (perturb X0 δ) 0) (HP - 1))
    (hhigh : ∀ j < N, 0 < j → NoCarry (blk d K N s (perturb X0 δ) j) HP) :
    PackingInput d K MC HP N s (perturb X0 δ) := by
  have hz : δ 0 = 0 := by
    by_contra hne
    have h := hpos 0 hne
    exact (Arithmetic.lt_irrefl (0 : V)) h
  have hX0 : perturb X0 δ 0 = X0 0 := by simp [perturb, hz]
  refine ⟨h0.N_gt, h0.s_lt, hhi, h0.MC_lt, h0.HP_pos, h0.HP_lt,
    hcell, ?_, hblk, ?_, ?_, hhigh0, hhigh⟩
  · simpa only [hX0] using h0.origin
  · simpa only [hX0] using h0.low_origin
  · intro j hj hjpos
    rcases le_one_iff_eq_zero_or_one.mp (hbool j) with hzero | hone
    · simpa [perturb, hzero] using h0.low j hj hjpos
    · simpa [perturb, hone] using hpulse j hj hjpos

#print axioms CompactPulsePreservationRetry.packing_of_pulse
end CompactPulsePreservationRetry
