import DiophantineConsistency.ArithmeticWangTableChunkA0
import DiophantineConsistency.ArithmeticWangTableChunkA1
import DiophantineConsistency.ArithmeticWangTableChunkA2
import DiophantineConsistency.ArithmeticWangTableChunkA3
import DiophantineConsistency.ArithmeticWangTableChunkA4
import DiophantineConsistency.ArithmeticWangTableChunkA5
import DiophantineConsistency.ArithmeticWangTableChunkA6
import DiophantineConsistency.ArithmeticWangTableChunkA7
import DiophantineConsistency.ArithmeticWangTableChunkB0
import DiophantineConsistency.ArithmeticWangTableChunkB1
import DiophantineConsistency.ArithmeticWangTableChunkB2
import DiophantineConsistency.ArithmeticWangTableChunkB3
import DiophantineConsistency.ArithmeticWangTableChunkB4
import DiophantineConsistency.ArithmeticWangTableChunkB5
import DiophantineConsistency.ArithmeticWangTableChunkB6
import DiophantineConsistency.ArithmeticWangTableChunkB7
import DiophantineConsistency.ArithmeticWangTableChunkC0
import DiophantineConsistency.ArithmeticWangTableChunkC1
import DiophantineConsistency.ArithmeticWangTableChunkC2
import DiophantineConsistency.ArithmeticWangTableChunkC3
import DiophantineConsistency.ArithmeticWangTableChunkC4
import DiophantineConsistency.ArithmeticWangTableChunkC5
import DiophantineConsistency.ArithmeticWangTableChunkC6
import DiophantineConsistency.ArithmeticWangTableChunkC7

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticWangTable
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open WangTiles942

private theorem combine {α : Type*} (P : α → Prop) (xs : List α)
    (hfirst : ∀ x ∈ xs.take 128, P x) (hrest : ∀ x ∈ xs.drop 128, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have h : x ∈ xs.take 128 ++ xs.drop 128 := by simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp h with h | h
  · exact hfirst x h
  · exact hrest x h

theorem rows_goodA : ∀ row ∈ orderedRows, GoodA row.2 := by
  have h7 : ∀ row ∈ orderedRows.drop 896, GoodA row.2 := rows_goodA_chunk7
  have h6 : ∀ row ∈ orderedRows.drop 768, GoodA row.2 := by
    apply combine (fun row => GoodA row.2) (orderedRows.drop 768)
    · exact rows_goodA_chunk6
    · simpa only [List.drop_drop, Nat.reduceAdd] using h7
  have h5 : ∀ row ∈ orderedRows.drop 640, GoodA row.2 := by
    apply combine (fun row => GoodA row.2) (orderedRows.drop 640)
    · exact rows_goodA_chunk5
    · simpa only [List.drop_drop, Nat.reduceAdd] using h6
  have h4 : ∀ row ∈ orderedRows.drop 512, GoodA row.2 := by
    apply combine (fun row => GoodA row.2) (orderedRows.drop 512)
    · exact rows_goodA_chunk4
    · simpa only [List.drop_drop, Nat.reduceAdd] using h5
  have h3 : ∀ row ∈ orderedRows.drop 384, GoodA row.2 := by
    apply combine (fun row => GoodA row.2) (orderedRows.drop 384)
    · exact rows_goodA_chunk3
    · simpa only [List.drop_drop, Nat.reduceAdd] using h4
  have h2 : ∀ row ∈ orderedRows.drop 256, GoodA row.2 := by
    apply combine (fun row => GoodA row.2) (orderedRows.drop 256)
    · exact rows_goodA_chunk2
    · simpa only [List.drop_drop, Nat.reduceAdd] using h3
  have h1 : ∀ row ∈ orderedRows.drop 128, GoodA row.2 := by
    apply combine (fun row => GoodA row.2) (orderedRows.drop 128)
    · exact rows_goodA_chunk1
    · simpa only [List.drop_drop, Nat.reduceAdd] using h2
  apply combine (fun row => GoodA row.2) orderedRows
  · exact rows_goodA_chunk0
  · exact h1

theorem rows_goodB : ∀ row ∈ orderedRows, GoodB row.2 := by
  have h7 : ∀ row ∈ orderedRows.drop 896, GoodB row.2 := rows_goodB_chunk7
  have h6 : ∀ row ∈ orderedRows.drop 768, GoodB row.2 := by
    apply combine (fun row => GoodB row.2) (orderedRows.drop 768)
    · exact rows_goodB_chunk6
    · simpa only [List.drop_drop, Nat.reduceAdd] using h7
  have h5 : ∀ row ∈ orderedRows.drop 640, GoodB row.2 := by
    apply combine (fun row => GoodB row.2) (orderedRows.drop 640)
    · exact rows_goodB_chunk5
    · simpa only [List.drop_drop, Nat.reduceAdd] using h6
  have h4 : ∀ row ∈ orderedRows.drop 512, GoodB row.2 := by
    apply combine (fun row => GoodB row.2) (orderedRows.drop 512)
    · exact rows_goodB_chunk4
    · simpa only [List.drop_drop, Nat.reduceAdd] using h5
  have h3 : ∀ row ∈ orderedRows.drop 384, GoodB row.2 := by
    apply combine (fun row => GoodB row.2) (orderedRows.drop 384)
    · exact rows_goodB_chunk3
    · simpa only [List.drop_drop, Nat.reduceAdd] using h4
  have h2 : ∀ row ∈ orderedRows.drop 256, GoodB row.2 := by
    apply combine (fun row => GoodB row.2) (orderedRows.drop 256)
    · exact rows_goodB_chunk2
    · simpa only [List.drop_drop, Nat.reduceAdd] using h3
  have h1 : ∀ row ∈ orderedRows.drop 128, GoodB row.2 := by
    apply combine (fun row => GoodB row.2) (orderedRows.drop 128)
    · exact rows_goodB_chunk1
    · simpa only [List.drop_drop, Nat.reduceAdd] using h2
  apply combine (fun row => GoodB row.2) orderedRows
  · exact rows_goodB_chunk0
  · exact h1

theorem rows_goodC : ∀ row ∈ orderedRows, GoodC row.2 := by
  have h7 : ∀ row ∈ orderedRows.drop 896, GoodC row.2 := rows_goodC_chunk7
  have h6 : ∀ row ∈ orderedRows.drop 768, GoodC row.2 := by
    apply combine (fun row => GoodC row.2) (orderedRows.drop 768)
    · exact rows_goodC_chunk6
    · simpa only [List.drop_drop, Nat.reduceAdd] using h7
  have h5 : ∀ row ∈ orderedRows.drop 640, GoodC row.2 := by
    apply combine (fun row => GoodC row.2) (orderedRows.drop 640)
    · exact rows_goodC_chunk5
    · simpa only [List.drop_drop, Nat.reduceAdd] using h6
  have h4 : ∀ row ∈ orderedRows.drop 512, GoodC row.2 := by
    apply combine (fun row => GoodC row.2) (orderedRows.drop 512)
    · exact rows_goodC_chunk4
    · simpa only [List.drop_drop, Nat.reduceAdd] using h5
  have h3 : ∀ row ∈ orderedRows.drop 384, GoodC row.2 := by
    apply combine (fun row => GoodC row.2) (orderedRows.drop 384)
    · exact rows_goodC_chunk3
    · simpa only [List.drop_drop, Nat.reduceAdd] using h4
  have h2 : ∀ row ∈ orderedRows.drop 256, GoodC row.2 := by
    apply combine (fun row => GoodC row.2) (orderedRows.drop 256)
    · exact rows_goodC_chunk2
    · simpa only [List.drop_drop, Nat.reduceAdd] using h3
  have h1 : ∀ row ∈ orderedRows.drop 128, GoodC row.2 := by
    apply combine (fun row => GoodC row.2) (orderedRows.drop 128)
    · exact rows_goodC_chunk1
    · simpa only [List.drop_drop, Nat.reduceAdd] using h2
  apply combine (fun row => GoodC row.2) orderedRows
  · exact rows_goodC_chunk0
  · exact h1

end DiophantineConsistency.ArithmeticWangTable
