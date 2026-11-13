import DiophantineConsistency.ArithmeticWangTableChunkBase
set_option autoImplicit false
namespace DiophantineConsistency.ArithmeticWangTable
theorem chunk_cover {α : Type*} (P : α → Prop) (xs : List α) (n : ℕ)
    (hleft : ∀ x ∈ xs.take n, P x) (hright : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hx' : x ∈ xs.take n ++ xs.drop n := by simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hx' with h | h
  · exact hleft x h
  · exact hright x h
#print axioms DiophantineConsistency.ArithmeticWangTable.chunk_cover
end DiophantineConsistency.ArithmeticWangTable
