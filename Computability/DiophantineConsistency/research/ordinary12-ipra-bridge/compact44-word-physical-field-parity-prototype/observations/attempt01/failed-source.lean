import CompactMarkedPhysicalColumn
import CompactWordLowSlot
import CompactWordFieldCyclic
import DiophantineConsistency.FieldWindowColumns

/-! Forward parity at the ordinary compact field phases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace CompactWordPhysicalFieldParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking CompactHeterogeneousCarry
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
open CompactConstructedWord CompactWordProperties CompactMarkedPhysicalColumn
open CompactWordLowSlot CompactWordFieldCyclic CompactAlignedTemporalBoolean CompactBitRotation
open CompactStencilZeroCarry
attribute [local irreducible] paramKernel rho selectors copies lowNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem vertical_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (u : ℕ) (hu : u<9) :
    dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j)
      ((1013+u:ℕ):V) % 2 = 0 := by
  let C := packedWord row dummy N
  let n : V := 8807*N
  let q : V := ((1013+u:ℕ):V)
  let k : V := 8807*j+q
  let T : V := temporalWord n (67*(8807*s)) C
  have hn : 0<n := mul_pos (by norm_num) hw.pos
  have hq : q<8807 := by dsimp [q]; exact_mod_cast (show 1013+u<8807 by omega)
  have hi := BlockCyclicIndex.index N j q hj hq
  have hk : k<n := hi.1
  have hp : k%8807=((1013+u:ℕ):V) := hi.2
  have hC : C<Exp.exp (67*n) := by
    dsimp [C,n]
    simpa only [mul_assoc] using packedWord_lt row dummy N
  have hslots : ∀ x<8807*N, 0<x → NoCarry (dig 67 C x) (dig 67 (lowNat:V) (x%8807)) := by
    intro x hx _
    exact word_low_slots row dummy hw hbool x hx
  obtain ⟨ha,hb,hbare⟩ := FieldWindowColumns.vertical N C k u hu hw.pos hk hC hp hslots
  have hphysical := (marked_physical_column row dummy hw hN hs hbool j hj q hq).2
  have hraw := RawParityBands.raw_mod_two position n C T k hn hk hC
  have heq := vertical_sources hw hj hs u hu (dummy:=dummy)
  have hrot : dig 67 (rot 67 n C (30%n)) k = dig 67 C (cyc n k 30) := by
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC, cyc_mod _ _ _ hn]
  have htemp : dig 67 T k = dig 67 C (cyc n k (8807*s)) := by
    dsimp only [T]
    rw [aligned_digit C n (8807*s) k hn hk hC, cyc_mod _ _ _ hn]
  change dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) q % 2 = 0
  rw [hphysical, show coeff = GenericBandCarryFamily.coefficient
    (fun x : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies x : V)) by rfl,
    hraw, ha, hb, hbare, hrot, htemp]
  simp only [zero_add]
  rw [heq]
  have htwo : dig 67 C (cyc n k (8807*s)) + dig 67 C (cyc n k (8807*s)) =
      dig 67 C (cyc n k (8807*s))*2 := by ring
  rw [htwo, mul_mod_right]

#print axioms CompactWordPhysicalFieldParity.vertical_even
end CompactWordPhysicalFieldParity
