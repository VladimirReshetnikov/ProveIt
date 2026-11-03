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
namespace CompactWordHorizontalParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking ArithmeticBinaryCarry CompactHeterogeneousCarry
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
open CompactConstructedWord CompactWordProperties CompactMarkedPhysicalColumn
open CompactWordLowSlot CompactWordFieldCyclic CompactAlignedTemporalBoolean CompactBitRotation
open CompactStencilZeroCarry
attribute [local irreducible] paramKernel rho selectors copies lowNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem horizontal_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (u : ℕ) (hu : u<8) :
    dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j)
      ((1065+u:ℕ):V) % 2 = 0 := by
  let C := packedWord row dummy N
  let n : V := 8807*N
  let q : V := ((1065+u:ℕ):V)
  let k : V := 8807*j+q
  let T : V := temporalWord n (67*(8807*s)) C
  have hn : 0<n := mul_pos (by norm_num) hw.pos
  have hq : q<8807 := by dsimp [q]; exact_mod_cast (show 1065+u<8807 by omega)
  have hi := BlockCyclicIndex.index N j q hj hq
  have hk : k<n := hi.1
  have hp : k%8807=((1065+u:ℕ):V) := hi.2
  have hC : C<Exp.exp (67*n) := by
    dsimp [C,n]
    simpa only [mul_assoc] using packedWord_lt row dummy N
  have hslots : ∀ x<8807*N, 0<x → NoCarry (dig 67 C x) (dig 67 (lowNat:V) (x%8807)) := by
    intro x hx _
    exact word_low_slots row dummy hw hbool x hx
  obtain ⟨ha,hb,hbare⟩ := FieldWindowColumns.horizontal N C k u hu hw.pos hk hC hp hslots
  have hphysical := (marked_physical_column row dummy hw hN hs hbool j hj q hq).2
  have hraw := RawParityBands.raw_mod_two position n C T k hn hk hC
  have heq := horizontal_sources hw hj u hu (dummy:=dummy)
  have hrot : dig 67 (rot 67 n C (62%n)) k = dig 67 C (cyc n k 62) := by
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC, cyc_mod _ _ _ hn]
  have hrot2 : dig 67 (rot 67 n C (8849%n)) k = dig 67 C (cyc n k 8849) := by
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC, cyc_mod _ _ _ hn]
  have htemp : dig 67 T k = 0 := by
    dsimp only [T]
    rw [aligned_digit C n (8807*s) k hn hk hC, cyc_mod _ _ _ hn,
      BlockCyclicIndex.shift N j s q hj hs hq]
    have hj' : cyc N j s < N := cyc_lt hw.pos _ _
    have hi' := BlockCyclicIndex.index N (cyc N j s) q hj' hq
    apply FieldExactZero.source_zero N C _ (1065+u) hi'.1 (by omega) hi'.2
      (FieldWindowGeometry.horizontal_temporal u hu) hslots
  change dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) q % 2 = 0
  rw [hphysical, show coeff = GenericBandCarryFamily.coefficient
    (fun x : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies x : V)) by rfl,
    hraw, ha, hb, hbare, hrot, hrot2, htemp]
  simp only [zero_add, add_zero]
  rw [heq]
  have htwo : dig 67 C (cyc n k 8849) + dig 67 C (cyc n k 8849) =
      dig 67 C (cyc n k 8849)*2 := by ring
  rw [htwo, mod_mul (by norm_num : (0:V)<2), mod_self, mul_zero, zero_mod]

#print axioms CompactWordHorizontalParity.horizontal_even
end CompactWordHorizontalParity
