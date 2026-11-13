import CompactMarkedTargetColumn
import CompactWordTargetNoCarry

/-! Exact high-mask no-carry at the two occupied target phases. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactMarkedTargetHighNoCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactConstructedWord CompactMarkedTargetColumn CompactWordTargetNoCarry
attribute [local irreducible] paramKernel rho highNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Both actual block digits avoid the exact symbolic high-mask digit. -/
theorem marked_targets_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (hN : 1 < N) (hs : s < N)
    (hbool : ∀ j, dummy j ≤ 1) (j : V) (hj : j < N) :
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 4393)
        (dig 67 (highNat : V) 4393) ∧
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 5495)
        (dig 67 (highNat : V) 5495) := by
  have ht := marked_targets row dummy hw hN hs hbool j hj
  constructor
  · rw [ht.1, HighMaskLocal.target4393]
    exact occupied_noCarry
  · rw [ht.2, HighMaskLocal.target5495]
    exact occupied_noCarry

#print axioms CompactMarkedTargetHighNoCarry.marked_targets_noCarry
end CompactMarkedTargetHighNoCarry
