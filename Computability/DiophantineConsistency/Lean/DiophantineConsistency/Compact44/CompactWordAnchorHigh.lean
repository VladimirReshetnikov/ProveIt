import DiophantineConsistency.Compact44.CompactWordAnchorParity
import DiophantineConsistency.Compact44.CompactBaseLowNoCarry
import DiophantineConsistency.Compact44.ParityPhase

/-! High-mask local no-carry at the two distant anchor phases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordAnchorHigh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticBinaryCarry ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactConstructedWord CompactWordAnchorParity CompactBaseLowNoCarry
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem phase2195_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 2195)
      (dig 67 (highNat : V) 2195) := by
  rw [ParityPhase.high2195]
  exact (noCarry_comm _ _).2 (one_noCarry_even _ (phase2195_even row dummy hw hN hs hbool hj))

theorem phase3296_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 3296)
      (dig 67 (highNat : V) 3296) := by
  rw [ParityPhase.high3296]
  exact (noCarry_comm _ _).2 (one_noCarry_even _ (phase3296_even row dummy hw hN hs hbool hj))

#print axioms CompactWordAnchorHigh.phase2195_noCarry
#print axioms CompactWordAnchorHigh.phase3296_noCarry
end CompactWordAnchorHigh
