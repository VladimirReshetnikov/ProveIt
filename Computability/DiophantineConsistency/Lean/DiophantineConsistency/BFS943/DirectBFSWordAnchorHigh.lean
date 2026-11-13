import DiophantineConsistency.BFS943.DirectBFSWordMarkerParity
import DiophantineConsistency.Compact44.CleanMaskClasses
import DiophantineConsistency.Compact44.ParityColumns
import DiophantineConsistency.Compact44.ParityPhase

/-! The constructed marked word has no digits outside the coarse Bad set. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSWordCleanSupport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits
open DirectBFSCellDigit DirectBFSCellDigitSupported DirectBFSConstructedWord DirectBFSLocalWord
open CleanGeometry CleanMaskClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cell_outside_bad (a d p : V) (ha : a ≠ 1) (hp : p < 8807)
    (hbad : ¬ Bad p) : cellDigit a d p = 0 := by
  by_contra hn
  obtain ⟨n, he, hs⟩ := cellDigit_supported a d p ha hp hn
  have hb : Bad (n : V) := (bad_cast n).2 (support_subset_bad n hs)
  apply hbad
  rw [he]
  exact hb

/-- No low-mask premise is used; support follows from the constructed digits. -/
theorem word_outside_bad (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : DirectBFSLocalWord.Word row N s) (k : V) (hk : k < 8807*N)
    (hbad : ¬ Bad (k%8807)) : dig 67 (packedWord row dummy N) k = 0 := by
  have hj : k/8807 < N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8807 < 8807 := mod_lt k (by norm_num)
  have he : 8807*(k/8807)+k%8807 = k := div_add_mod k 8807
  rw [← he, word_digit row dummy N _ _ hj hp]
  exact cell_outside_bad (row (k/8807)) (dummy (k/8807)%2) _ (hw.tile_ne _ hj) hp hbad

#print axioms DirectBFSWordCleanSupport.cell_outside_bad
#print axioms DirectBFSWordCleanSupport.word_outside_bad
end DirectBFSWordCleanSupport

/-! Forward parity at the distant compact anchor phases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectBFSWordAnchorParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking CompactHeterogeneousCarry
open CompactSymbolicKernel DirectBFSSymbolicKernel CompactSymbolicPorts DirectBFSLocalWord
open CompactGenericAlignedMass DirectBFSModelMass CompactTwoBandFlatten
open DirectBFSConstructedWord DirectBFSPhysicalColumn
open DirectBFSWordMarkerParity DirectBFSWordCleanSupport CompactAlignedTemporalBoolean CompactBitRotation
open DirectBFSStencilZeroCarry CompactPartialBandRotation CleanGeometry
attribute [local irreducible] paramKernel rho selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem phase2195_even (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : DirectBFSLocalWord.Word row N s) (hN : 1<N) (hs : s<N)
    (hj : j<N) :
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
  have hphysical := (physical_column row dummy hw hN hs j hj 2195 (by norm_num)).2
  have hraw := DirectBFSRawParity.raw_mod_two position n C T k hn hk hC
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
    {N s j : V} (hw : DirectBFSLocalWord.Word row N s) (hN : 1<N) (hs : s<N)
    (hj : j<N) :
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
  have hphysical := (physical_column row dummy hw hN hs j hj 3296 (by norm_num)).2
  have hraw := DirectBFSRawParity.raw_mod_two position n C T k hn hk hC
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

#print axioms DirectBFSWordAnchorParity.phase2195_even
#print axioms DirectBFSWordAnchorParity.phase3296_even
end DirectBFSWordAnchorParity

/-! High-mask local no-carry at the two distant anchor phases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSWordAnchorHigh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticBinaryCarry ArithmeticPacking
open CompactSymbolicKernel DirectBFSSymbolicKernel CompactSymbolicPorts DirectBFSLocalWord
open DirectBFSConstructedWord DirectBFSWordAnchorParity DirectBFSBaseLowNoCarry
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem phase2195_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : DirectBFSLocalWord.Word row N s) (hN : 1<N) (hs : s<N)
    (hj : j<N) :
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 2195)
      (dig 67 (highNat : V) 2195) := by
  rw [ParityPhase.high2195]
  exact (noCarry_comm _ _).2 (one_noCarry_even _ (phase2195_even row dummy hw hN hs hj))

theorem phase3296_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j : V} (hw : DirectBFSLocalWord.Word row N s) (hN : 1<N) (hs : s<N)
    (hj : j<N) :
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 3296)
      (dig 67 (highNat : V) 3296) := by
  rw [ParityPhase.high3296]
  exact (noCarry_comm _ _).2 (one_noCarry_even _ (phase3296_even row dummy hw hN hs hj))

#print axioms DirectBFSWordAnchorHigh.phase2195_noCarry
#print axioms DirectBFSWordAnchorHigh.phase3296_noCarry
end DirectBFSWordAnchorHigh
