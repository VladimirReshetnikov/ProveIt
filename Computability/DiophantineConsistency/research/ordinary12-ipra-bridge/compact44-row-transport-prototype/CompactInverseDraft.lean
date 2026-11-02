import DiophantineConsistency.CompactRowComplete
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace CompactInverseDraft
open DiophantineConsistency CompactRelabelDraft CompactTableLookup CompactRowTransport
open DiophantineConsistency.ArithmeticWangTable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def inverseLookup (j : V) : V := tabValue inverseRows.toList 0 j

theorem forward_natural (m : ℕ) (hm : m < 942) :
    inverseRows[rowIndices.toList.getD m 0]?.getD 999 = m := by
  have hr : m < rowIndices.toList.length := by simpa only [row_length] using hm
  have h := congrArg (fun xs : List ℕ => xs[m]?) forward_roundtrip
  simp only [forwardRoundtrip, List.getElem?_map,
    getElem?_pos rowIndices.toList m hr, getElem?_pos (List.range 942) m (by simpa using hm),
    List.getElem_range, Option.map_some, Option.some.injEq] at h
  simpa only [List.getD_eq_getElem?_getD, getElem?_pos rowIndices.toList m hr,
    Option.getD_some] using h

/-- The exact inverse-array lookup is a left inverse on the old row range. -/
theorem inverse_forward {i : V} (hi : i < 942) : inverseLookup (rowLookup i) = i := by
  obtain ⟨m,hm,rfl⟩ := standard_of_lt (n := 942) (by simpa using hi)
  have hr : m < rowIndices.toList.length := by simpa only [row_length] using hm
  have hmem : rowIndices.toList[m] ∈ rowIndices.toList := List.getElem_mem _
  have hv : rowIndices.toList[m] = 0 ∨ (2 ≤ rowIndices.toList[m] ∧ rowIndices.toList[m] < 943) :=
    of_decide_eq_true ((List.all_eq_true.mp valid_indices) _ hmem)
  have hbound : rowIndices.toList[m] < inverseRows.size := by
    have sz : inverseRows.size = 943 := by decide +kernel
    omega
  dsimp only [rowLookup, inverseLookup]
  rw [tab_cast, List.getD_eq_getElem?_getD, getElem?_pos rowIndices.toList m hr]
  simp only [Option.getD_some]
  rw [tab_cast, List.getD_eq_getElem?_getD]
  have hn := forward_natural m hm
  simp only [List.getD_eq_getElem?_getD, getElem?_pos rowIndices.toList m hr,
    Option.getD_some, getElem?_pos inverseRows _ hbound, Option.getD_some] at hn
  simpa [getElem?_pos inverseRows _ hbound, hn]
#print axioms CompactInverseDraft.inverse_forward
end CompactInverseDraft
namespace CompactInverseDraft
open DiophantineConsistency CompactRelabelDraft CompactTableLookup CompactRowTransport
open DiophantineConsistency.ArithmeticWangTable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem inverse_image {j : V} (hj : j < 943) (hne : j ≠ 1) :
    inverseLookup j < 942 ∧ rowLookup (inverseLookup j) = j := by
  obtain ⟨i,hi,he⟩ := row_surjective hj hne
  rw [← he, inverse_forward hi]
  exact ⟨hi, rfl⟩

/-- `inverseLookup` is a finite table lookup; a later definability client must
    explicitly use `tab_defined` and prove composition with the marked word. -/
instance inverseLookup_defined : 𝚺₀-Function₁[V] inverseLookup :=
  (tab_defined inverseRows.toList 0).to_definable
#print axioms CompactInverseDraft.inverse_image
end CompactInverseDraft
