import DiophantineConsistency.Sign17KStreamReversal

/-! SOURCE ONLY. A single finite-vector increment as list set. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KStreamBump

theorem ofFn_bump (n : ℕ) (v : Fin n → ℕ) (k : Fin n) :
    List.ofFn (fun i => v i + if i = k then 1 else 0) =
      (List.ofFn v).set k.val (v k + 1) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_set]
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_set, List.length_ofFn]
    by_cases he : i = k.val
    · subst i
      simp
    · have hk : (⟨i, by simpa only [List.length_ofFn] using h₁⟩ : Fin n) ≠ k := by
        intro heq
        exact he (congrArg Fin.val heq)
      simp [he, Ne.symm he, hk]

theorem block_as_reverse_set (v : Fin 986 → ℕ) :
    Sign17KRadixStream.block v =
      ((List.ofFn v).reverse).set 984 (v ⟨1, by decide⟩ + 1) := by
  unfold Sign17KRadixStream.block
  rw [ofFn_bump, Sign17KStreamReversal.ofFn_rev]
  rfl

end DiophantineConsistency.Sign17KStreamBump
#print axioms DiophantineConsistency.Sign17KStreamBump.ofFn_bump
#print axioms DiophantineConsistency.Sign17KStreamBump.block_as_reverse_set
