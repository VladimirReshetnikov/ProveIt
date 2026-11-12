import DiophantineConsistency.Compact44.CompactMaskBoundFinish
import DiophantineConsistency.Compact44.CompactSymbolicPorts
import DiophantineConsistency.ArithmeticStandardCasts

/-! Source-only narrow copy of the existing compact port bounds proof.
No Mixed121 source, Lean elaboration or provider claim. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.CompactPortBoundsSlimDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem port_bounds (B K L H : ℕ) (hB : (B : V) + 1 = Exp.exp ((67 : V) * 8807))
    (hL : L = lowNat) (hH : H = highNat) :
    0 < (ports B K L H 0 : V) ∧ (ports B K L H 2 : V) < (ports B K L H 0 : V) ∧
      (ports B K L H 3 : V) < 2 * (ports B K L H 0 : V) ∧ (46 : V) ≤ (ports B K L H 0 : V) := by
  obtain ⟨hb, hl', hh', _⟩ := CompactMaskBoundFinish.bounds (B : V) 1 hB (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < (B : V); exact hb
  · change (L : V) < (B : V); rw [hL]; exact hl'
  · change ((B + H : ℕ) : V) < 2 * (B : V); rw [Nat.cast_add, hH]; exact hh'
  · have h64 : (64 : V) = Exp.exp (6 : V) := by
      have h := ArithmeticStandardCasts.cast_exp (V := V) 6
      norm_num at h
      exact h.symm
    have hbig : (64 : V) ≤ (B : V) + 1 := by
      rw [hB, h64]; exact exp_monotone_le.mpr (by norm_num)
    change (46 : V) ≤ (B : V)
    apply le_iff_lt_succ.mpr
    exact lt_of_lt_of_le (by norm_num : (46 : V) < 64) hbig

end DiophantineConsistency.CompactPortBoundsSlimDraft

#print axioms DiophantineConsistency.CompactPortBoundsSlimDraft.port_bounds
