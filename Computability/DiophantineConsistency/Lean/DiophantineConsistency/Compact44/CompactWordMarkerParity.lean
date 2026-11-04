import DiophantineConsistency.Compact44.CompactMarkedPhysicalColumn
import DiophantineConsistency.Compact44.CompactWordLowSlot
import DiophantineConsistency.Compact44.CompactWordAnchorBits
import DiophantineConsistency.Compact44.FieldMarkerColumns
import DiophantineConsistency.Compact44.MarkerBlockIndex

/-! Forward parity at the two fixed-marker compact field phases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace CompactWordMarkerParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking ArithmeticBinaryCarry CompactHeterogeneousCarry
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
open CompactForwardCellInputs CompactWordCellClient CompactConstructedWord CompactWordProperties
open CompactMarkedPhysicalColumn CompactWordLowSlot CompactWordAnchorBits
open CompactAlignedTemporalBoolean CompactBitRotation CompactStencilZeroCarry
attribute [local irreducible] paramKernel rho selectors copies lowNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every fixed anchor bit occurs at its designated copy slot. -/
theorem marker_digit (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hj : j<N) (i : Fin 7) (p : ℕ)
    (hp : position ⟨34+i.val,by have := i.isLt; omega⟩=p) :
    dig 67 (packedWord row dummy N) (8807*j+(p:V)) = 1 := by
  let slot : Fin 41 := ⟨34+i.val, by have := i.isLt; omega⟩
  have hc := word_copy row dummy N j hj slot
  have ha := row_anchor (row j) (hw.tile_lt j hj) i
  change dig 67 (packedWord row dummy N) (8807*j+(position slot:V)) =
    fbit (payload (row j)) ((34+i.val:ℕ):V) at hc
  rw [hp] at hc
  exact hc.trans ha

/-- At vertical marker phase 1022 both surviving sources are fixed ones. -/
theorem vertical_marker_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 1022 % 2 = 0 := by
  let C := packedWord row dummy N
  let n : V := 8807*N
  let k : V := 8807*j+1022
  let T : V := temporalWord n (67*(8807*s)) C
  have hn : 0<n := mul_pos (by norm_num) hw.pos
  have hi := BlockCyclicIndex.index N j (1022:V) hj (by norm_num)
  have hk : k<n := hi.1
  have hp : k%8807=(1022:V) := hi.2
  have hC : C<Exp.exp (67*n) := by dsimp [C,n]; simpa only [mul_assoc] using packedWord_lt row dummy N
  have hslots : ∀ x<8807*N, 0<x → NoCarry (dig 67 C x) (dig 67 (lowNat:V) (x%8807)) := by
    intro x hx _; exact word_low_slots row dummy hw hbool x hx
  obtain ⟨ha,hb,hbare⟩ := FieldMarkerColumns.vertical N C k hw.pos hk hC hp hslots
  have hphysical := (marked_physical_column row dummy hw hN hs hbool j hj 1022 (by norm_num)).2
  have hraw := RawParityBands.raw_mod_two position n C T k hn hk hC
  have hrot : dig 67 (rot 67 n C (30%n)) k = 1 := by
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC, cyc_mod _ _ _ hn,
      BlockCyclicIndex.reflected N j 1022 30 hj (by norm_num) (by norm_num)]
    have hsub : (1022:V)-30=992 := (eq_tsub_of_add_eq (by norm_num : (992:V)+30=1022)).symm
    rw [hsub]
    exact marker_digit row dummy hw hj ⟨3,by decide⟩ 992 (by decide)
  have htemp : dig 67 T k = 1 := by
    dsimp only [T]
    rw [aligned_digit C n (8807*s) k hn hk hC, cyc_mod _ _ _ hn,
      BlockCyclicIndex.shift N j s 1022 hj hs (by norm_num)]
    exact marker_digit row dummy hw (cyc_lt hw.pos _ _) ⟨1,by decide⟩ 1022 (by decide)
  change dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 1022 % 2 = 0
  rw [hphysical, show coeff = GenericBandCarryFamily.coefficient
    (fun x : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies x : V)) by rfl,
    hraw, ha, hb, hbare, hrot, htemp]
  norm_num

/-- At horizontal marker phase 1073 both surviving bare sources are fixed
ones, while the temporal contribution is absent. -/
theorem horizontal_marker_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 1073 % 2 = 0 := by
  let C := packedWord row dummy N
  let n : V := 8807*N
  let k : V := 8807*j+1073
  let T : V := temporalWord n (67*(8807*s)) C
  have hn : 0<n := mul_pos (by norm_num) hw.pos
  have hi := BlockCyclicIndex.index N j (1073:V) hj (by norm_num)
  have hk : k<n := hi.1
  have hp : k%8807=(1073:V) := hi.2
  have hC : C<Exp.exp (67*n) := by dsimp [C,n]; simpa only [mul_assoc] using packedWord_lt row dummy N
  have hslots : ∀ x<8807*N, 0<x → NoCarry (dig 67 C x) (dig 67 (lowNat:V) (x%8807)) := by
    intro x hx _; exact word_low_slots row dummy hw hbool x hx
  obtain ⟨ha,hb,hbare⟩ := FieldMarkerColumns.horizontal N C k hw.pos hk hC hp hslots
  have hphysical := (marked_physical_column row dummy hw hN hs hbool j hj 1073 (by norm_num)).2
  have hraw := RawParityBands.raw_mod_two position n C T k hn hk hC
  have hrot1 : dig 67 (rot 67 n C (62%n)) k = 1 := by
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC, cyc_mod _ _ _ hn,
      BlockCyclicIndex.reflected N j 1073 62 hj (by norm_num) (by norm_num)]
    have hsub : (1073:V)-62=1011 := (eq_tsub_of_add_eq (by norm_num : (1011:V)+62=1073)).symm
    rw [hsub]
    exact marker_digit row dummy hw hj ⟨2,by decide⟩ 1011 (by decide)
  have hrot2 : dig 67 (rot 67 n C (8849%n)) k = 1 := by
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC, cyc_mod _ _ _ hn,
      MarkerBlockIndex.previous N j hw.pos hj]
    exact marker_digit row dummy hw (cyc_lt hw.pos _ _) ⟨0,by decide⟩ 1031 (by decide)
  have htemp : dig 67 T k = 0 := by
    dsimp only [T]
    rw [aligned_digit C n (8807*s) k hn hk hC, cyc_mod _ _ _ hn,
      BlockCyclicIndex.shift N j s 1073 hj hs (by norm_num)]
    have hj' : cyc N j s<N := cyc_lt hw.pos _ _
    have hi' := BlockCyclicIndex.index N (cyc N j s) (1073:V) hj' (by norm_num)
    exact FieldExactZero.source_zero N C _ 1073 hi'.1 (by norm_num) hi'.2
      HorizontalMarkerGeometry.temporal_absent hslots
  rw [hphysical, show coeff = GenericBandCarryFamily.coefficient
    (fun x : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies x : V)) by rfl,
    hraw, ha, hb, hbare, hrot1, hrot2, htemp]
  norm_num

#print axioms CompactWordMarkerParity.marker_digit
#print axioms CompactWordMarkerParity.vertical_marker_even
#print axioms CompactWordMarkerParity.horizontal_marker_even
end CompactWordMarkerParity
