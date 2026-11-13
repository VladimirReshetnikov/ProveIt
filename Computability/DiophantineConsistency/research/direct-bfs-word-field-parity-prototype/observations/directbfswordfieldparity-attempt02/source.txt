import DirectBFSPhysicalColumn
import DirectBFSWordFieldCyclic
import DirectBFSWordLowFields
import CompactSymbolicMaskData
import DiophantineConsistency.FieldWindowColumns
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectBFSWordFieldParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking ArithmeticPackingBlocks ArithmeticBinaryCarry CompactHeterogeneousCarry
open CompactSymbolicKernel DirectBFSSymbolicKernel CompactSymbolicPorts DirectBFSLocalWord
open CompactGenericAlignedMass DirectBFSModelMass CompactTwoBandFlatten
open DirectBFSConstructedWord DirectBFSUniformPackedCell DirectBFSCellLowPulse DirectBFSPhysicalColumn
open DirectBFSWordFieldCyclic CompactAlignedTemporalBoolean CompactBitRotation DirectBFSStencilZeroCarry
open CompactPartialBandRotation
attribute [local irreducible] paramKernel rho selectors copies lowNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem word_low_slots (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : DirectBFSLocalWord.Word row N s) :
    ∀ k < 8807*N, NoCarry (dig 67 (packedWord row dummy N) k) (dig 67 (lowNat : V) (k%8807)) := by
  let X : V → V := cellWord row dummy
  letI : 𝚺₁-Function₁ X := word_definable row dummy
  have hX : ∀ j < N, X j < Exp.exp (67*8807) := fun j _ => word_cell_lt row dummy j
  intro k hk
  have hj : k/8807 < N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8807 < 8807 := mod_lt k (by norm_num)
  have he : 8807*(k/8807)+k%8807 = k := div_add_mod k 8807
  have hd : dig 67 (packedWord row dummy N) k = dig 67 (X (k/8807)) (k%8807) := by
    calc
      dig 67 (packedWord row dummy N) k =
          dig 67 (packedWord row dummy N) (8807*(k/8807)+k%8807) := by rw [he]
      _ = dig 67 (dig (67*8807) (packedWord row dummy N) (k/8807)) (k%8807) :=
        (subdigit _ _ _ hp).symm
      _ = dig 67 (X (k/8807)) (k%8807) := by
        change dig 67 (dig (67*8807) (bsum (67*8807) X N) (k/8807)) _ = _
        rw [dig_bsum hX hj]
  rw [hd]
  apply noCarry_dig 67 (X (k/8807)) (lowNat : V) (k%8807)
  rw [CompactSymbolicMaskData.low_eq]
  exact normalized_noCarry (row (k/8807)) (dummy (k/8807)) (hw.tile_ne _ hj)

theorem vertical_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : DirectBFSLocalWord.Word row N s) (hN : 1<N) (hs : s<N)
    (hj : j<N) (u : ℕ) (hu : u<9) :
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
    exact word_low_slots row dummy hw x hx
  obtain ⟨ha,hb,hbare⟩ := FieldWindowColumns.vertical N C k u hu hw.pos hk hC hp hslots
  have hphysical := (physical_column row dummy hw hN hs j hj q hq).2
  have hraw := DirectBFSRawParity.raw_mod_two position n C T k hn hk hC
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
  rw [htwo, mod_mul (by norm_num : (0:V)<2), mod_self, mul_zero, zero_mod]


theorem horizontal_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : DirectBFSLocalWord.Word row N s) (hN : 1<N) (hs : s<N)
    (hj : j<N) (u : ℕ) (hu : u<8) :
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
    exact word_low_slots row dummy hw x hx
  obtain ⟨ha,hb,hbare⟩ := FieldWindowColumns.horizontal N C k u hu hw.pos hk hC hp hslots
  have hphysical := (physical_column row dummy hw hN hs j hj q hq).2
  have hraw := DirectBFSRawParity.raw_mod_two position n C T k hn hk hC
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


#print axioms DirectBFSWordFieldParity.word_low_slots
#print axioms DirectBFSWordFieldParity.vertical_even
#print axioms DirectBFSWordFieldParity.horizontal_even
end DirectBFSWordFieldParity
