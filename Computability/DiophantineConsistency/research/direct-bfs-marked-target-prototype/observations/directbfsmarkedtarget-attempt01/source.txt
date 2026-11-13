import DirectBFSWordAnchorHigh
import DirectBFSWordOccupied
import DirectBFSUniformForeign
import CompactWordTargetNoCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSMarkedTarget
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking ArithmeticBinaryCarry CompactHeterogeneousCarry
open CompactSymbolicKernel DirectBFSSymbolicKernel CompactSymbolicPorts DirectBFSLocalWord
open CompactGenericAlignedMass DirectBFSModelMass CompactTwoBandFlatten
open DirectBFSConstructedWord DirectBFSPhysicalColumn DirectBFSWordFieldParity DirectBFSWordCleanSupport
open CompactAlignedTemporalBoolean DirectBFSStencilZeroCarry CompactBitRotation CompactPartialBandRotation CompactPartialBand
open DirectBFSRawColumn CompactWordTargetNoCarry RawColumnBands CleanGeometry
attribute [local irreducible] paramKernel rho selectors copies highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_index (n j : V) (T e : ℕ) (hk : 8807*j+(T:V)<n) (he : e≤T) :
    cyc n (8807*j+(T:V)) (((T-e:ℕ)):V) = 8807*j+(e:V) := by
  have hs : (e:V)+(((T-e:ℕ)):V)=(T:V) := by exact_mod_cast Nat.add_sub_of_le he
  have hoffle : (((T-e:ℕ)):V)≤8807*j+(T:V) := by
    rw [←hs]
    have h : (((T-e:ℕ)):V)≤(e:V)+(((T-e:ℕ)):V) := le_add_of_nonneg_left (by simp)
    exact le_trans h (le_add_of_nonneg_left (by simp))
  have hoff : (((T-e:ℕ)):V)<n := lt_of_le_of_lt hoffle hk
  rw [cyc_of_le hk hoff hoffle]
  apply (eq_tsub_of_add_eq ?_).symm
  rw [←hs]
  ring

/-- The selected reflected band's actual rotated-column sum is the word
cell aggregate, for either target `T ≥ 4393`, provided the packed word has
the indicated selector and payload digits. -/
theorem selected_band {b : V → V} {N s j n C : V} (hword : DirectBFSLocalWord.Word b N s)
    (hj : j<N) (T : ℕ) (hT : 4393≤T) (hn : 0<n)
    (hk : 8807*j+(T:V)<n) (hC : C<Exp.exp (67*n))
    (hsel : ∀ i : Fin 943, dig 67 C (8807*j+(i.val:V))=wordSelector b i j)
    (hcopy : ∀ i : Fin 41, dig 67 C (8807*j+(position i:V))=wordPayloadBit b i j) :
    DirectBFSRawColumn.columnBand position T n C (8807*j+(T:V)) = 1+Exp.exp 51 := by
  have hs (i : Fin 943) : selectorDigit n C (8807*j+(T:V)) T i = wordSelector b i j := by
    unfold selectorDigit
    rw [source_index n j T i.val hk (by have := i.isLt; omega), hsel]
  have hc (i : Fin 41) : copyDigit position n C (8807*j+(T:V)) T i = wordPayloadBit b i j := by
    unfold copyDigit
    rw [source_index n j T (position i) hk (by have := position_lt_target i; omega), hcopy]
  rw [DirectBFSRawColumn.band_column position T n C _ hn hk hC, ← DirectBFSCoefficientDecoder.finite_decomposition]
  simp_rw [hs, hc]
  simpa only [DirectBFSModelMass.selectors, DirectBFSModelMass.copies] using
    (DirectBFSWordOccupied.word_occupied hword hj)


theorem marked_targets (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : DirectBFSLocalWord.Word row N s) (hN : 1 < N) (hs : s < N)
    (j : V) (hj : j < N) :
    dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 4393 = 1 + Exp.exp 51 ∧
    dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 5495 = 1 + Exp.exp 51 := by
  let C : V := packedWord row dummy N
  let n : V := 8807*N
  let T : V := temporalWord n (67*(8807*s)) C
  have hn : 0 < n := mul_pos (by norm_num) hw.pos
  have hC : C < Exp.exp (67*n) := by
    simpa only [C, n, mul_assoc] using packedWord_lt row dummy N
  have hzero : ∀ k < n, ¬Bad (k%8807) → dig 67 C k = 0 := by
    apply CleanModelSupport.zero_outside n C
    intro k hk _
    exact word_low_slots row dummy hw k hk
  have hidx (q : V) (hq : q < 8807) :
      8807*j+q < n ∧ (8807*j+q)%8807 = q :=
    BlockCyclicIndex.index N j q hj hq
  have htemporal (q : V) (hq : q < 8807) (hbad : ¬Bad q) :
      dig 67 T (8807*j+q) = 0 := by
    have hqidx := hidx q hq
    have hoff : 8807*s < n := mul_lt_mul_of_pos_left hs (by norm_num)
    have hprev : cyc N j s < N := cyc_lt hw.pos j s
    rw [show T = temporalWord n (67*(8807*s)) C by rfl,
      aligned_digit C n (8807*s) (8807*j+q) hn hqidx.1 hC,
      mod_eq_self_of_lt hoff, BlockCyclicIndex.shift N j s q hj hs hq]
    have htarget := BlockCyclicIndex.index N (cyc N j s) q hprev hq
    apply hzero _ htarget.1
    rw [htarget.2]
    exact hbad
  have hsel : ∀ i : Fin 943, dig 67 C (8807*j+(i.val:V)) = wordSelector row i j :=
    word_selector row dummy N j hj
  have hcopy : ∀ i : Fin 41, dig 67 C (8807*j+(position i:V)) = wordPayloadBit row i j :=
    word_copy row dummy N j hj
  have htarget1 := selected_band hw hj 4393 (by norm_num) hn (hidx 4393 (by norm_num)).1 hC hsel hcopy
  have htarget2 := selected_band hw hj 5495 (by norm_num) hn (hidx 5495 (by norm_num)).1 hC hsel hcopy
  simp only [Nat.cast_ofNat] at htarget1 htarget2
  have hforeign1 := DirectBFSUniformForeign.at4393 N C (8807*j+4393) hw.pos
    (hidx 4393 (by norm_num)).1 hC hzero (hidx 4393 (by norm_num)).2
  have hforeign2 := DirectBFSUniformForeign.at5495 N C (8807*j+5495) hw.pos
    (hidx 5495 (by norm_num)).1 hC hzero (hidx 5495 (by norm_num)).2
  have ht1 : dig 67 T (8807*j+4393) = 0 := htemporal 4393 (by norm_num) (by unfold Bad; norm_num)
  have ht2 : dig 67 T (8807*j+5495) = 0 := htemporal 5495 (by norm_num) (by unfold Bad; norm_num)
  have hr1 := DirectBFSRawColumn.flatten position n C T (8807*j+4393)
  have hr2 := DirectBFSRawColumn.flatten position n C T (8807*j+5495)
  change raw 67 (coeff : DirectBFSStencilZeroCarry.Idx → V) (GenericBandCarryFamily.word n C (bandOffsets position) T) _ = _ at hr1 hr2
  rw [htarget1, hforeign1.1, hforeign1.2, ht1] at hr1
  rw [hforeign2.1, htarget2, hforeign2.2, ht2] at hr2
  simp only [zero_add, add_zero] at hr1 hr2
  have hp1 := (physical_column row dummy hw hN hs j hj 4393 (by norm_num)).2
  have hp2 := (physical_column row dummy hw hN hs j hj 5495 (by norm_num)).2
  exact ⟨hp1.trans hr1, hp2.trans hr2⟩


theorem marked_targets_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : DirectBFSLocalWord.Word row N s) (hN : 1 < N) (hs : s < N)
    (j : V) (hj : j < N) :
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 4393)
        (dig 67 (highNat : V) 4393) ∧
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) 5495)
        (dig 67 (highNat : V) 5495) := by
  have ht := marked_targets row dummy hw hN hs j hj
  constructor
  · rw [ht.1, HighMaskLocal.target4393]
    exact occupied_noCarry
  · rw [ht.2, HighMaskLocal.target5495]
    exact occupied_noCarry


#print axioms DirectBFSMarkedTarget.selected_band
#print axioms DirectBFSMarkedTarget.marked_targets
#print axioms DirectBFSMarkedTarget.marked_targets_noCarry
end DirectBFSMarkedTarget
