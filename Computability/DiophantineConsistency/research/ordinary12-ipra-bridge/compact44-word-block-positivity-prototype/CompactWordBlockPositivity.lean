import CompactWordPackingFields

/-! Compact word cells and their normalized transport blocks are positive. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordBlockPositivity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking
open CompactMarkedTransport CompactForwardCellInputs CompactPackedCell CompactWordLowFields

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A valid row sets its own selector digit to one. -/
theorem packedCell_pos (a d : V) (ha : a < 943) (hd : d ≤ 1) :
    0 < packedCell a d := by
  obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 943) ha
  have hn : n < 943 := by exact_mod_cast ha
  have h := packedCell_selector (n : V) d hd ⟨n, hn⟩
  have hs : dig 67 (packedCell (n : V) d) (n : V) = 1 := by
    simpa [selector] using h
  by_contra hzero
  have he : packedCell (n : V) d = 0 :=
    le_antisymm (not_lt.mp hzero) (Arithmetic.zero_le _)
  rw [he] at hs
  simp [dig] at hs

/-- Both base and pulsed words have positive normalized blocks everywhere,
because every cyclic temporal predecessor is a positive cell. -/
theorem block_pos {row δ : V → V} {d K N s : V}
    (hw : CompactWord row N s) (j : V) :
    0 < blk d K N s (baseCell row) j ∧
    0 < blk d K N s (pulsedCell row δ) j := by
  have hk : cyc N j s < N := cyc_lt hw.pos j s
  have hp : 0 < baseCell row (cyc N j s) :=
    packedCell_pos (row _) 0 (hw.tile_lt _ hk) (by simp)
  have hq : 0 < pulsedCell row δ (cyc N j s) :=
    lt_of_lt_of_le hp (le_add_of_nonneg_right (Arithmetic.zero_le _))
  constructor <;> unfold blk
  · exact lt_of_lt_of_le hp (le_add_of_nonneg_left (Arithmetic.zero_le _))
  · exact lt_of_lt_of_le hq (le_add_of_nonneg_left (Arithmetic.zero_le _))

#print axioms CompactWordBlockPositivity.packedCell_pos
#print axioms CompactWordBlockPositivity.block_pos
end CompactWordBlockPositivity
