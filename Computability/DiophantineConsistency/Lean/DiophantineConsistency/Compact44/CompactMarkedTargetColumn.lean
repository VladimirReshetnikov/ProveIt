import DiophantineConsistency.Compact44.CompactMarkedPhysicalColumn
import DiophantineConsistency.Compact44.CompactWordLowSlot
import DiophantineConsistency.Compact44.CompactWordProductColumn
import DiophantineConsistency.Compact44.UniformForeignZero
import DiophantineConsistency.Compact44.BlockCyclicIndex

/-! The two clause-target columns of every marked compact word. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactMarkedTargetColumn
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking CompactHeterogeneousCarry
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactMarkedTransport
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
open CompactConstructedWord CompactWordProperties CompactWordLowSlot CompactWordCellClient
open CompactMarkedPhysicalColumn CompactWordProductColumn CompactAlignedTemporalBoolean
open CompactStencilZeroCarry CompactBitRotation CompactPartialBandRotation RawColumnBands CleanGeometry
attribute [local irreducible] paramKernel rho selectors copies

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Both target digits contain exactly the selected occupied aggregate.
No full packing or high-mask assumption is used. -/
theorem marked_targets (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (hN : 1 < N) (hs : s < N)
    (hbool : ∀ j, dummy j ≤ 1) (j : V) (hj : j < N) :
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
    exact word_low_slots row dummy hw hbool k hk
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
  have hforeign1 := UniformForeignZero.at4393 N C (8807*j+4393) hw.pos
    (hidx 4393 (by norm_num)).1 hC hzero (hidx 4393 (by norm_num)).2
  have hforeign2 := UniformForeignZero.at5495 N C (8807*j+5495) hw.pos
    (hidx 5495 (by norm_num)).1 hC hzero (hidx 5495 (by norm_num)).2
  have ht1 : dig 67 T (8807*j+4393) = 0 := htemporal 4393 (by norm_num) (by unfold Bad; norm_num)
  have ht2 : dig 67 T (8807*j+5495) = 0 := htemporal 5495 (by norm_num) (by unfold Bad; norm_num)
  have hr1 := RawColumnBands.flatten position n C T (8807*j+4393)
  have hr2 := RawColumnBands.flatten position n C T (8807*j+5495)
  change raw 67 (coeff : CompactStencilZeroCarry.Idx → V) (GenericBandCarryFamily.word n C (bandOffsets position) T) _ = _ at hr1 hr2
  rw [htarget1, hforeign1.1, hforeign1.2, ht1] at hr1
  rw [hforeign2.1, htarget2, hforeign2.2, ht2] at hr2
  simp only [zero_add, add_zero] at hr1 hr2
  have hp1 := (marked_physical_column row dummy hw hN hs hbool j hj 4393 (by norm_num)).2
  have hp2 := (marked_physical_column row dummy hw hN hs hbool j hj 5495 (by norm_num)).2
  exact ⟨hp1.trans hr1, hp2.trans hr2⟩

#print axioms CompactMarkedTargetColumn.marked_targets
end CompactMarkedTargetColumn
