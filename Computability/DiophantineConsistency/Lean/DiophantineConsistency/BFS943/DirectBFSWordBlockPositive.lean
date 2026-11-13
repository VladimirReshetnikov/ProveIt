import DiophantineConsistency.BFS943.DirectBFSConstructedWord
import DiophantineConsistency.ArithmeticPacking
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSWordBlockPositive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking
open CompactForwardCellInputs DirectBFSPackedCell DirectBFSUniformPackedCell DirectBFSConstructedWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem packedCell_pos (a d : V) (ha : a<943) (hd : d≤1) : 0<packedCell a d := by
  obtain ⟨n,rfl⟩ := eq_nat_of_lt_nat (n:=943) ha
  have hn : n<943 := by exact_mod_cast ha
  have h := packedCell_selector (n:V) d hd ⟨n,hn⟩
  have hs : dig 67 (packedCell (n:V) d) (n:V)=1 := by simpa [selector] using h
  by_contra hzero
  have he : packedCell (n:V) d=0 := le_antisymm (not_lt.mp hzero) (Arithmetic.zero_le _)
  rw [he] at hs
  simp [dig] at hs

theorem block_pos {row dummy : V → V} {d K N s : V}
    (hw : DirectBFSLocalWord.Word row N s) (j : V) :
    0<blk d K N s (cellWord row dummy) j := by
  have hk : cyc N j s<N := cyc_lt hw.pos j s
  have hd : dummy (cyc N j s)%2≤1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
  have hp : 0<cellWord row dummy (cyc N j s) :=
    packedCell_pos (row _) (dummy _%2) (hw.tile_lt _ hk) hd
  unfold blk
  exact lt_of_lt_of_le hp (le_add_of_nonneg_left (Arithmetic.zero_le _))
#print axioms DirectBFSWordBlockPositive.packedCell_pos
#print axioms DirectBFSWordBlockPositive.block_pos
end DirectBFSWordBlockPositive
