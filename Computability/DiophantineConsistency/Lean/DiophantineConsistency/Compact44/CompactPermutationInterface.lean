import DiophantineConsistency.ArithmeticWangTable
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactPermutationInterface
variable {α : Type*} [BEq α] [LawfulBEq α]

def indexEquiv {xs ys : List α} (h : xs.Perm ys) : Fin xs.length ≃ Fin ys.length where
  toFun := h.idxBij
  invFun := h.symm.idxBij
  left_inv := h.idxBij_symm_leftInverse_idxBij
  right_inv := h.idxBij_symm_rightInverse_idxBij

theorem lookup_preserved {xs ys : List α} (h : xs.Perm ys) (i : Fin xs.length) :
    ys[(indexEquiv h i).val] = xs[i.val] := by
  exact h.getElem_idxBij_eq_getElem i

theorem range_lookup {xs : List ℕ} {n : ℕ} (h : xs.Perm (List.range n))
    (i : Fin xs.length) : (indexEquiv h i).val = xs[i.val] := by
  have he := lookup_preserved h i
  simpa only [List.getElem_range] using he
section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWangTable
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_lookup_injective {xs : List ℕ} {n : ℕ} (hp : xs.Perm (List.range n))
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
  have hnd : xs.Nodup := hp.symm.nodup List.nodup_range
  have hab := hnd.injective_get hn
  exact congrArg (fun k : Fin xs.length => (k.val : V)) hab

theorem model_lookup_surjective {xs : List ℕ} {n : ℕ} (hp : xs.Perm (List.range n))
    {a : V} (ha : a < (n : V)) :
    ∃ i : V, i < (xs.length : V) ∧ tabValue xs 0 i = a := by
  obtain ⟨m,hm,rfl⟩ := standard_of_lt ha
  have hmem : m ∈ xs := hp.mem_iff.mpr (List.mem_range.mpr hm)
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨(i : V), ?_, ?_⟩
  · exact_mod_cast hi
  · rw [tab_cast]
    simp [List.getD_eq_getElem?_getD, hi, he]
end Model
end CompactPermutationInterface
#print axioms CompactPermutationInterface.model_lookup_injective
#print axioms CompactPermutationInterface.model_lookup_surjective
#print axioms CompactPermutationInterface.lookup_preserved
#print axioms CompactPermutationInterface.range_lookup
