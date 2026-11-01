import BusyBeaver.ZFC.FiniteControlTable254

set_option autoImplicit false

/-!
Catalogue sources by a structural rank witness through the finite binary tree.
`pathRank` and `pathEdge` compute the false-first leaf rank and the edge at the
end of a path, walking only the path (right steps add the left subtree's leaf
count). `source_of_path` turns the two computations into the exact catalogue
source, so no catalogue list is built or indexed by reduction, and default
proof limits are retained.
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

end AtRank

/-- This derives the complete existing catalogue source; it creates no new program. -/
theorem source_of_atRank {q : Control} {P : List Bool} {e : Edge}
    (h : AtRank ActualTree254.tree q.val P e) : source q = (P, e) := by
  have hv := h.lookup
  rw [List.getElem?_eq_getElem (by
    rw [leafEntries_length]
    exact h.bound)] at hv
  exact Option.some.inj hv

/-- The false-first leaf rank reached by a path: every right step skips the
leaves of the left subtree. Only the path and those left counts are computed. -/
def pathRank : Tree → List Bool → Nat
  | .node a _, false :: P => pathRank a P
  | .node a b, true :: P => leafCount a + pathRank b P
  | _, _ => 0

/-- The edge at the end of a path that ends exactly at a leaf. -/
def pathEdge : Tree → List Bool → Option Edge
  | .leaf e, [] => some e
  | .node a _, false :: P => pathEdge a P
  | .node _ b, true :: P => pathEdge b P
  | _, _ => none

/-- A computed path lookup is a structural rank witness. -/
theorem atRank_of_pathEdge : ∀ (t : Tree) (P : List Bool) (e : Edge),
    pathEdge t P = some e → AtRank t (pathRank t P) P e
  | .leaf e', [], e, h => by cases Option.some.inj h; exact .here e'
  | .node a _, false :: P, e, h => .left (atRank_of_pathEdge a P e h)
  | .node _ b, true :: P, e, h => .right (atRank_of_pathEdge b P e h)
  | .none, _, _, h => by simp [pathEdge] at h
  | .leaf _, _ :: _, _, h => by simp [pathEdge] at h
  | .node _ _, [], _, h => by simp [pathEdge] at h

/-- Catalogue sources from a computed path lookup, at default proof limits. -/
theorem source_of_path {q : Control} {P : List Bool} {e : Edge}
    (hr : pathRank ActualTree254.tree P = q.val) (he : pathEdge ActualTree254.tree P = some e) :
    source q = (P, e) :=
  source_of_atRank (hr ▸ atRank_of_pathEdge _ _ _ he)

/-- Resolve a literal target through its finite tree path, avoiding catalogue search. -/
theorem literal_target (P : List Bool) (q : Control)
    (hw : RMBisim.twalk ActualTree254.tree P 0 =
      some ((source q).2, (source q).1.length))
    (hc : consume P (source q).1.length = (source q).1) : resolveControl P = q := by
  have hw' : walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 =
      some ((source q).2, (source q).1.length) := by
    rw [RMBisim.walk_root, ActualTree254.tree_eq]
    exact hw
  apply source_injective
  rw [resolve_source _ _ _ hw', hc]

/-- Rewrite only abstract source equalities before checking the finite path. -/
theorem cached_target {a b : Control} {P Q : List Bool} {e f : Edge}
    (ha : source a = (P, e)) (hb : source b = (Q, f))
    (next : List Bool → List Bool)
    (hw : RMBisim.twalk ActualTree254.tree (next P) 0 = some (f, Q.length))
    (hc : consume (next P) Q.length = Q) :
    resolveControl (next (source a).1) = b := by
  rw [ha]
  apply literal_target
  · simpa only [hb] using hw
  · simpa only [hb] using hc

/-- Literal catalogue source at rank354, obtained from the tree witness. -/
theorem source_354 :
    source (⟨354, by decide⟩ : Control) =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, false, false], .decnz 1) :=
  source_of_path (by rfl) (by rfl)

/-- Literal catalogue source at rank6423, obtained from the tree witness. -/
theorem source_6423 :
    source (⟨6423, by decide⟩ : Control) =
      ([true, true, true, true, true, false, false, false], .decnz 6) :=
  source_of_path (by rfl) (by rfl)

end SetTheory.BusyBeaver.ZFC.ArithmeticControlSourceRank254
