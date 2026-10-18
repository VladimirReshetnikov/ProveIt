import BusyBeaver.ZFC.FiniteControlTable254

set_option autoImplicit false

/-!
Source-only prototype: certify a false-first catalogue rank through a finite
binary tree. The witness follows a tree path, and right steps carry the left
subtree's leaf count. No list prefix is dropped or indexed by reduction in the
actual source-equality clients. Default proof limits are retained.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlSourceRank254
open RegisterPath RMBisim SiteCoverage FiniteControlTable254

/-- A structural witness for an exact path, edge and false-first leaf rank. -/
inductive AtRank : Tree → Nat → List Bool → Edge → Prop where
  | here (e : Edge) : AtRank (.leaf e) 0 [] e
  | left {a b : Tree} {i : Nat} {P : List Bool} {e : Edge} :
      AtRank a i P e → AtRank (.node a b) i (false :: P) e
  | right {a b : Tree} {i : Nat} {P : List Bool} {e : Edge} :
      AtRank b i P e → AtRank (.node a b) (leafCount a + i) (true :: P) e

namespace AtRank

/-- Bounds follow structurally, with no traversal of the catalogue list. -/
theorem bound {t : Tree} {i : Nat} {P : List Bool} {e : Edge}
    (h : AtRank t i P e) : i < leafCount t := by
  induction h with
  | here => exact Nat.zero_lt_succ 0
  | left _ ih => exact Nat.lt_of_lt_of_le ih (Nat.le_add_right _ _)
  | right _ ih => exact Nat.add_lt_add_left ih _

/-- The catalogue lookup agrees with the structural rank witness. -/
theorem lookup {t : Tree} {i : Nat} {P : List Bool} {e : Edge}
    (h : AtRank t i P e) : (leafEntries t)[i]? = some (P, e) := by
  induction h with
  | here => rfl
  | left h ih =>
    rw [leafEntries, List.getElem?_append_left (by
      simpa only [List.length_map, leafEntries_length] using h.bound),
      List.getElem?_map, ih]
    rfl
  | right h ih =>
    rw [leafEntries, List.getElem?_append_right (by
      simp only [List.length_map, leafEntries_length]
      exact Nat.le_add_right _ _),
      List.length_map, leafEntries_length, Nat.add_sub_cancel_left,
      List.getElem?_map, ih]
    rfl

/-- A separately checked count can be reused at many literal right steps. -/
theorem right_count {a b : Tree} {n i : Nat} {P : List Bool} {e : Edge}
    (hn : leafCount a = n) (h : AtRank b i P e) :
    AtRank (.node a b) (n + i) (true :: P) e := by
  rw [← hn]
  exact .right h

end AtRank

/-- This derives the complete existing catalogue source; it creates no new program. -/
theorem source_of_atRank {q : Control} {P : List Bool} {e : Edge}
    (h : AtRank ActualTree254.tree q.val P e) : source q = (P, e) := by
  have hv := h.lookup
  rw [List.getElem?_eq_getElem (by
    rw [leafEntries_length]
    exact h.bound)] at hv
  exact Option.some.inj hv

private theorem rank_354 :
    AtRank ActualTree254.tree 354 [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, false, false] (.decnz 1) := by
  apply AtRank.right_count (n := 10) (i := 344) (by rfl)
  apply AtRank.right_count (n := 14) (i := 330) (by rfl)
  apply AtRank.right_count (n := 14) (i := 316) (by rfl)
  apply AtRank.left
  apply AtRank.right_count (n := 1) (i := 315) (by rfl)
  apply AtRank.left
  apply AtRank.left
  apply AtRank.right_count (n := 1) (i := 314) (by rfl)
  apply AtRank.left
  apply AtRank.left
  apply AtRank.right_count (n := 1) (i := 313) (by rfl)
  apply AtRank.left
  apply AtRank.right_count (n := 81) (i := 232) (by rfl)
  apply AtRank.left
  apply AtRank.left
  apply AtRank.right_count (n := 153) (i := 79) (by rfl)
  apply AtRank.right_count (n := 79) (i := 0) (by rfl)
  apply AtRank.left
  apply AtRank.left
  apply AtRank.left
  apply AtRank.left
  exact .here _

/-- Literal catalogue source at rank354, obtained from the tree witness. -/
theorem source_354 :
    source (⟨354, by decide⟩ : Control) =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, false, false], .decnz 1) := source_of_atRank rank_354

private theorem rank_6423 :
    AtRank ActualTree254.tree 6423 [true, true, true, true, true, false, false, false] (.decnz 6) := by
  apply AtRank.right_count (n := 10) (i := 6413) (by rfl)
  apply AtRank.right_count (n := 14) (i := 6399) (by rfl)
  apply AtRank.right_count (n := 14) (i := 6385) (by rfl)
  apply AtRank.right_count (n := 6329) (i := 56) (by rfl)
  apply AtRank.right_count (n := 56) (i := 0) (by rfl)
  apply AtRank.left
  apply AtRank.left
  apply AtRank.left
  exact .here _

/-- Literal catalogue source at rank6423, obtained from the tree witness. -/
theorem source_6423 :
    source (⟨6423, by decide⟩ : Control) =
      ([true, true, true, true, true, false, false, false], .decnz 6) := source_of_atRank rank_6423

end SetTheory.BusyBeaver.ZFC.ArithmeticControlSourceRank254
