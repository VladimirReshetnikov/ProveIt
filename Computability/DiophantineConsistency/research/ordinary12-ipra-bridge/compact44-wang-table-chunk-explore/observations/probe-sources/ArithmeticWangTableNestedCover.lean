import DiophantineConsistency.ArithmeticWangTableChunkCover
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticWangTable
theorem nested_cover {α : Type*} (P : α → Prop) (xs : List α)
    (h0 : ∀ x ∈ xs.take 32, P x)
    (h1 : ∀ x ∈ (xs.drop 32).take 32, P x)
    (h2 : ∀ x ∈ xs.drop 64, P x) : ∀ x ∈ xs, P x := by
  apply chunk_cover P xs 32 h0
  apply chunk_cover P (xs.drop 32) 32 h1
  simpa only [List.drop_drop, show 32+32=64 by decide] using h2
#print axioms DiophantineConsistency.ArithmeticWangTable.nested_cover
end DiophantineConsistency.ArithmeticWangTable
