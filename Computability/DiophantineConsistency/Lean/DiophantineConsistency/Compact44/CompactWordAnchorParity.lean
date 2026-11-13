import DiophantineConsistency.Compact44.CompactWordMarkerParity
import DiophantineConsistency.Compact44.CompactWordCleanSupport
import DiophantineConsistency.Compact44.ParityColumns

/-! Forward parity at the distant compact anchor phases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace CompactWordAnchorParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking CompactHeterogeneousCarry
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
open CompactConstructedWord CompactWordProperties CompactMarkedPhysicalColumn
open CompactWordMarkerParity CompactWordCleanSupport CompactAlignedTemporalBoolean CompactBitRotation
open CompactStencilZeroCarry CleanGeometry
attribute [local irreducible] paramKernel rho selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem phase2195_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 2195 % 2 = 0 := by
  let C := packedWord row dummy N
  let n : V := 8807*N
  let k : V := 8807*j+2195
  let T : V := temporalWord n (67*(8807*s)) C
  have hn : 0<n := mul_pos (by norm_num) hw.pos
  have hi := BlockCyclicIndex.index N j (2195:V) hj (by norm_num)
  have hk : k<n := hi.1
  have hp : k%8807=(2195:V) := hi.2
  have hC : C<Exp.exp (67*n) := by dsimp [C,n]; simpa only [mul_assoc] using packedWord_lt row dummy N
  have hzero : ∀ t<8807*N, ¬Bad (t%8807) → dig 67 C t=0 := by
    intro t ht hbad
    exact word_outside_bad row dummy hw t ht hbad
  obtain ⟨ha,hb,hbare⟩ := ParityColumns.at2195 N C k hw.pos hk hC hzero hp
  have hphysical := (marked_physical_column row dummy hw hN hs hbool j hj 2195 (by norm_num)).2
  have hraw := RawParityBands.raw_mod_two position n C T k hn hk hC
  have hrot : dig 67 C (cyc n k 1100) = 1 := by
    rw [BlockCyclicIndex.reflected N j 2195 1100 hj (by norm_num) (by norm_num)]
    have hsub : (2195:V)-1100=1095 := (eq_tsub_of_add_eq (by norm_num : (1095:V)+1100=2195)).symm
    rw [hsub]
    exact marker_digit row dummy hw hj ⟨4,by decide⟩ 1095 (by decide)
  have htemp : dig 67 T k = 1 := by
    dsimp only [T]
    rw [aligned_digit C n (8807*s) k hn hk hC, cyc_mod _ _ _ hn,
      BlockCyclicIndex.shift N j s 2195 hj hs (by norm_num)]
    exact marker_digit row dummy hw (cyc_lt hw.pos _ _) ⟨5,by decide⟩ 2195 (by decide)
  rw [hphysical, show coeff = GenericBandCarryFamily.coefficient
    (fun x : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies x : V)) by rfl,
    hraw, ha, hb, hbare, hrot, htemp]
  norm_num

theorem phase3296_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) :
    dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 3296 % 2 = 0 := by
  let C := packedWord row dummy N
  let n : V := 8807*N
  let k : V := 8807*j+3296
  let T : V := temporalWord n (67*(8807*s)) C
  have hn : 0<n := mul_pos (by norm_num) hw.pos
  have hi := BlockCyclicIndex.index N j (3296:V) hj (by norm_num)
  have hk : k<n := hi.1
  have hp : k%8807=(3296:V) := hi.2
  have hC : C<Exp.exp (67*n) := by dsimp [C,n]; simpa only [mul_assoc] using packedWord_lt row dummy N
  have hzero : ∀ t<8807*N, ¬Bad (t%8807) → dig 67 C t=0 := by
    intro t ht hbad
    exact word_outside_bad row dummy hw t ht hbad
  obtain ⟨ha,hb,hbare⟩ := ParityColumns.at3296 N C k hw.pos hk hC hzero hp
  have hphysical := (marked_physical_column row dummy hw hN hs hbool j hj 3296 (by norm_num)).2
  have hraw := RawParityBands.raw_mod_two position n C T k hn hk hC
  have hrot : dig 67 C (cyc n k 2201) = 1 := by
    rw [BlockCyclicIndex.reflected N j 3296 2201 hj (by norm_num) (by norm_num)]
    have hsub : (3296:V)-2201=1095 := (eq_tsub_of_add_eq (by norm_num : (1095:V)+2201=3296)).symm
    rw [hsub]
    exact marker_digit row dummy hw hj ⟨4,by decide⟩ 1095 (by decide)
  have htemp : dig 67 T k = 1 := by
    dsimp only [T]
    rw [aligned_digit C n (8807*s) k hn hk hC, cyc_mod _ _ _ hn,
      BlockCyclicIndex.shift N j s 3296 hj hs (by norm_num)]
    exact marker_digit row dummy hw (cyc_lt hw.pos _ _) ⟨6,by decide⟩ 3296 (by decide)
  rw [hphysical, show coeff = GenericBandCarryFamily.coefficient
    (fun x : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies x : V)) by rfl,
    hraw, ha, hb, hbare, hrot, htemp]
  norm_num

#print axioms CompactWordAnchorParity.phase2195_even
#print axioms CompactWordAnchorParity.phase3296_even
end CompactWordAnchorParity
