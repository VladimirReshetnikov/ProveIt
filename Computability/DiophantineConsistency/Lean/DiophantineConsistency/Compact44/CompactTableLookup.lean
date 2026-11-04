import DiophantineConsistency.Compact44.CompactRelabelFinal
import DiophantineConsistency.Compact44.CompactPermutationInterface
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactTableLookup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWangTable CompactPermutationInterface CompactRelabelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def horizontalLookup (i : V) : V := tabValue horizontal.toList 0 i
noncomputable def verticalLookup (i : V) : V := tabValue vertical.toList 0 i
noncomputable def rowLookup (i : V) : V := tabValue rowIndices.toList 0 i

theorem horizontal_length : horizontal.toList.length = 250 := by decide +kernel
theorem vertical_length : vertical.toList.length = 439 := by decide +kernel
theorem row_length : rowIndices.toList.length = 942 := by decide +kernel

theorem horizontal_injective {i j : V} (hi : i < 250) (hj : j < 250)
    (h : horizontalLookup i = horizontalLookup j) : i = j := by
  apply model_lookup_injective horizontal_permutation (xs:=horizontal.toList) (n:=250)
  · simpa only [horizontal_length, Nat.cast_ofNat] using hi
  · simpa only [horizontal_length, Nat.cast_ofNat] using hj
  · exact h

theorem horizontal_surjective {v : V} (hv : v < 250) :
    ∃ i : V, i < 250 ∧ horizontalLookup i = v := by
  obtain ⟨i,hi,hvalue⟩ := model_lookup_surjective horizontal_permutation (xs:=horizontal.toList) (n:=250) hv
  exact ⟨i, by simpa only [horizontal_length, Nat.cast_ofNat] using hi, hvalue⟩

theorem vertical_injective {i j : V} (hi : i < 439) (hj : j < 439)
    (h : verticalLookup i = verticalLookup j) : i = j := by
  apply model_lookup_injective vertical_permutation (xs:=vertical.toList) (n:=439)
  · simpa only [vertical_length, Nat.cast_ofNat] using hi
  · simpa only [vertical_length, Nat.cast_ofNat] using hj
  · exact h

theorem vertical_surjective {v : V} (hv : v < 439) :
    ∃ i : V, i < 439 ∧ verticalLookup i = v := by
  obtain ⟨i,hi,hvalue⟩ := model_lookup_surjective vertical_permutation (xs:=vertical.toList) (n:=439) hv
  exact ⟨i, by simpa only [vertical_length, Nat.cast_ofNat] using hi, hvalue⟩

/-- Generic source-list injectivity is enough for a target range with one omitted value. -/
theorem nodup_lookup_injective {xs : List ℕ} (hnd : xs.Nodup)
    {i j : V} (hi : i < (xs.length : V)) (hj : j < (xs.length : V))
    (he : tabValue xs 0 i = tabValue xs 0 j) : i = j := by
  obtain ⟨a,ha,rfl⟩ := standard_of_lt hi
  obtain ⟨b,hb,rfl⟩ := standard_of_lt hj
  have hget (m : ℕ) (hm : m < xs.length) :
      tabValue xs 0 (m : V) = ((xs.get ⟨m,hm⟩ : ℕ) : V) := by
    rw [tab_cast]
    simp [List.getD_eq_getElem?_getD, hm]
  rw [hget a ha,hget b hb] at he
  have hn : xs.get ⟨a,ha⟩ = xs.get ⟨b,hb⟩ := by exact_mod_cast he
  have hab := hnd.injective_get hn
  exact congrArg (fun k : Fin xs.length => (k.val : V)) hab

theorem row_injective {i j : V} (hi : i < 942) (hj : j < 942)
    (h : rowLookup i = rowLookup j) : i = j := by
  apply nodup_lookup_injective index_nodup
  · simpa only [row_length, Nat.cast_ofNat] using hi
  · simpa only [row_length, Nat.cast_ofNat] using hj
  · exact h

theorem row_surjective {v : V} (hv : v < 943) (hne : v ≠ 1) :
    ∃ i : V, i < 942 ∧ rowLookup i = v := by
  obtain ⟨m,hm,rfl⟩ := standard_of_lt (n:=943) (by simpa using hv)
  have hmne : m ≠ 1 := by
    intro h
    apply hne
    simp only [h, Nat.cast_one]
  have hmem : m ∈ compactIndices := by
    simp only [compactIndices, List.mem_append, List.mem_singleton]
    by_cases hz : m = 0
    · exact Or.inl hz
    · right
      apply List.mem_range'.2
      refine ⟨m-2, by omega, ?_⟩
      omega
  have hrow : m ∈ rowIndices.toList := indices_permutation.mem_iff.mpr hmem
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hrow
  refine ⟨(i : V), ?_, ?_⟩
  · have hi' : i < 942 := by simpa only [row_length] using hi
    exact_mod_cast hi'
  · have he' : rowIndices.toList.getD i 0 = m := by
      rw [List.getD_eq_getElem?_getD, getElem?_pos rowIndices.toList i hi]
      simp only [Option.getD_some]
      exact he
    dsimp only [rowLookup]
    rw [tab_cast, he']
end CompactTableLookup
#print axioms CompactTableLookup.row_injective
#print axioms CompactTableLookup.row_surjective
#print axioms CompactTableLookup.horizontal_injective
#print axioms CompactTableLookup.horizontal_surjective
#print axioms CompactTableLookup.vertical_injective
#print axioms CompactTableLookup.vertical_surjective
