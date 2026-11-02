import DiophantineConsistency.CompactRowComplete
import DiophantineConsistency.ArithmeticWangPlane
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace CompactMarkedTransport
open DiophantineConsistency CompactRelabelDraft CompactTableLookup CompactRowTransport
open DiophantineConsistency.ArithmeticWangTable DiophantineConsistency.ArithmeticWangPlane
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem row_image {i : V} (hi : i < 942) : rowLookup i < 943 ∧ rowLookup i ≠ 1 := by
  obtain ⟨m, hm, rfl⟩ := standard_of_lt (n := 942) (by simpa using hi)
  have hr : m < rowIndices.toList.length := by simpa only [row_length] using hm
  have hmem : rowIndices.toList[m] ∈ rowIndices.toList := List.getElem_mem _
  have hv : rowIndices.toList[m] = 0 ∨ (2 ≤ rowIndices.toList[m] ∧ rowIndices.toList[m] < 943) :=
    of_decide_eq_true ((List.all_eq_true.mp valid_indices) _ hmem)
  have hn : rowIndices.toList[m] < 943 := by omega
  have hne : rowIndices.toList[m] ≠ 1 := by omega
  dsimp only [rowLookup]
  rw [tab_cast, List.getD_eq_getElem?_getD, getElem?_pos rowIndices.toList m hr]
  simp only [Option.getD_some]
  constructor
  · exact_mod_cast hn
  · exact_mod_cast hne

theorem row_zero : rowLookup (0 : V) = 0 := by
  change tabValue rowIndices.toList 0 ((0 : ℕ) : V) = 0
  rw [tab_cast]
  norm_num [rowIndices]

/-- A cyclic compact word with the extra tile explicitly excluded. -/
structure CompactWord (b : V → V) (N s : V) : Prop where
  pos : 0 < N
  tile_lt : ∀ j < N, b j < 943
  tile_ne : ∀ j < N, b j ≠ 1
  marker : b 0 = 0
  east : ∀ j < N, ∀ j' < N, (j' + 1) % N = j →
    compactField (fun t => t.2.2.1) (b j) = compactField (fun t => t.1) (b j')
  south : ∀ j < N, ∀ j' < N, (j' + s) % N = j →
    compactField (fun t => t.2.2.2) (b j) = compactField (fun t => t.2.1) (b j')

theorem forward_marked_word {a : V → V} {N s : V} (h : MarkedWord a N s) :
    CompactWord (fun j => rowLookup (a j)) N s := by
  refine ⟨h.pos, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; exact (row_image (h.tile_lt j hj)).1
  · intro j hj; exact (row_image (h.tile_lt j hj)).2
  · rw [h.marker]; exact row_zero
  · intro j hj j' hj' he
    exact (horizontal_match_bounded (h.tile_lt j hj) (h.tile_lt j' hj')).2 (h.east j hj j' hj' he)
  · intro j hj j' hj' he
    exact (vertical_match_bounded (h.tile_lt j hj) (h.tile_lt j' hj')).2 (h.south j hj j' hj' he)
#print axioms CompactMarkedTransport.forward_marked_word
end CompactMarkedTransport
