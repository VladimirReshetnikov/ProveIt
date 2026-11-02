import DiophantineConsistency.CompactTableLookup
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace CompactRowTransport
open DiophantineConsistency CompactRelabelDraft
open DiophantineConsistency.ArithmeticWangTable

theorem row_at (m : ℕ) (hm : m < 942) :
    translated (tileN m) =
      Compact943Data.rows.toArray[rowIndices.toList.getD m 0]?.getD (0,0,0,0) := by
  have hr : m < rowIndices.toList.length := by simpa only [CompactTableLookup.row_length] using hm
  have ho : m < WangTiles942.orderedRows.length := by simpa only [WangTiles942.ordered_count] using hm
  have h := congrArg (fun xs => xs[m]?) full_row_equality
  simp only [mappedOld, selectedNew, List.getElem?_map, getElem?_pos WangTiles942.orderedRows m ho,
    getElem?_pos rowIndices.toList m hr, Option.map_some, Option.some.injEq] at h
  simpa only [tileN, dif_pos hm, WangTiles942.tile, List.getD_eq_getElem?_getD,
    getElem?_pos rowIndices.toList m hr, Option.getD_some] using h
#print axioms CompactRowTransport.row_at
end CompactRowTransport

namespace CompactRowTransport
open DiophantineConsistency CompactRelabelDraft
open DiophantineConsistency.ArithmeticWangTable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
abbrev Quad := ℕ × ℕ × ℕ × ℕ
noncomputable def compactField (f : Quad → ℕ) (i : V) : V :=
  tabValue (Compact943Data.rows.map f) 0 i

theorem compactField_cast (f : Quad → ℕ) (hf : f (0,0,0,0) = 0) (m : ℕ) :
    compactField f (m : V) = ((f (Compact943Data.rows.toArray[m]?.getD (0,0,0,0))) : V) := by
  dsimp only [compactField]
  rw [tab_cast, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : Compact943Data.rows[m]? <;> simp [h, hf]

theorem bounded_row_fields {i : V} (hi : i < 942) :
    ∃ m : ℕ, m < 942 ∧ i = (m : V) ∧
      (let j := rowIndices.toList.getD m 0
       CompactTableLookup.rowLookup i = (j : V) ∧
       translated (tileN m) = Compact943Data.rows.toArray[j]?.getD (0,0,0,0)) := by
  obtain ⟨m, hm, rfl⟩ := standard_of_lt (n := 942) (by simpa using hi)
  refine ⟨m, hm, rfl, ?_⟩
  constructor
  · exact tab_cast _ _
  · exact row_at m hm
theorem bounded_field_transport (f : Quad → ℕ) (hf : f (0,0,0,0) = 0)
    {i : V} (hi : i < 942) :
    ∃ m : ℕ, m < 942 ∧ i = (m : V) ∧
      compactField f (CompactTableLookup.rowLookup i) = ((f (translated (tileN m))) : V) := by
  obtain ⟨m, hm, hindex, hrow, htile⟩ := bounded_row_fields hi
  refine ⟨m, hm, hindex, ?_⟩
  rw [hrow, compactField_cast f hf, htile]
#print axioms CompactRowTransport.bounded_field_transport
#print axioms CompactRowTransport.compactField_cast
#print axioms CompactRowTransport.bounded_row_fields
end CompactRowTransport
