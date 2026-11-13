import CompactHighPhaseReduction
import CompactMarkedHighPadding
import CompactMarkedCellSum
import CompactWordFieldHigh
import CompactMarkedTargetHighNoCarry
import CompactWordAnchorHigh
import CompactWordPhaseZeroHigh

/-! Assemble all symbolic high-mask phase classes for actual compact blocks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace CompactMarkedAllHigh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticBinaryCarry ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactConstructedWord CompactWordPulseEquality CompactPackedCell CompactCanonicalPerturbation
open CompactHighPhaseReduction CompactMarkedHighPadding CompactMarkedCellSum
open CompactWordFieldHigh CompactMarkedTargetHighNoCarry CompactWordAnchorHigh CompactWordPhaseZeroHigh
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Actual normalized blocks avoid the complete symbolic high mask. -/
theorem marked_all_high (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) :
    ∀ j<N, NoCarry (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) (highNat : V) := by
  let X0 : V → V := fun j => packedCell (row j) 0
  have he : cellWord row dummy = perturb X0 dummy := by
    funext j
    exact cellWord_boolean_pulse row dummy j (hbool j)
  have hpads := (marked_padding row dummy hw (fun j _ => hbool j)).2
  have hsums := (marked_cell_sums row dummy hw (fun j _ => hbool j)).2
  intro j hj
  apply noCarry_of_active
  · have hsum := hsums j hj
    rw [← he] at hsum
    have hb := lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le (cellWord row dummy j))) hsum
    simpa only [show (67*8807 : V) = 590069 by norm_num] using hb
  · intro p _ hp
    rw [he]
    exact hpads j hj p hp
  · intro p _ ha
    rcases ha with h0 | hv | hh | h1 | h2 | h3 | h4
    · rw [h0]
      exact phase_zero_noCarry (row:=row) (dummy:=dummy) (j:=j) hw
    · exact vertical_fields row dummy hw hN hs hbool hj hv.1 hv.2
    · exact horizontal_fields row dummy hw hN hs hbool hj hh.1 hh.2
    · rw [h1]; exact phase2195_noCarry row dummy hw hN hs hbool hj
    · rw [h2]; exact phase3296_noCarry row dummy hw hN hs hbool hj
    · rw [h3]; exact (marked_targets_noCarry row dummy hw hN hs hbool j hj).1
    · rw [h4]; exact (marked_targets_noCarry row dummy hw hN hs hbool j hj).2

#print axioms CompactMarkedAllHigh.marked_all_high
end CompactMarkedAllHigh
