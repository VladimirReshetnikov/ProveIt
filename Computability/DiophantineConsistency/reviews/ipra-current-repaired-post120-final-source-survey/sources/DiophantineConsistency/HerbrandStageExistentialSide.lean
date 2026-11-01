import DiophantineConsistency.HerbrandUniversalTree
import DiophantineConsistency.HerbrandInteractiveFourTriple
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandStageExistentialSide
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax HerbrandUniversalTree HerbrandInteractiveFourTriple

theorem neg_prefix_tree {ξ : Type} {n : ℕ} (φ : Semiformula language ξ n)
    (h : UniversalPrefix φ) : ExistentialTree (∼φ) := by
  induction φ using Semiformula.rec' with
  | hall p ih => exact ExistentialTree.ex (ih h)
  | hverum => exact ExistentialTree.base (Semiformula.open_neg.mpr h)
  | hfalsum => exact ExistentialTree.base (Semiformula.open_neg.mpr h)
  | hrel r v => exact ExistentialTree.base (Semiformula.open_neg.mpr h)
  | hnrel r v => exact ExistentialTree.base (Semiformula.open_neg.mpr h)
  | hand p q ihp ihq => exact ExistentialTree.base (Semiformula.open_neg.mpr h)
  | hor p q ihp ihq => exact ExistentialTree.base (Semiformula.open_neg.mpr h)
  | hexs p ih => exact ExistentialTree.base (Semiformula.open_neg.mpr h)

theorem bad_neg_tree (r j : ℕ) (ψ : Semiproposition language 7)
    (hψ : UniversalPrefix ψ) : ExistentialTree (∼(bad r j ψ)) := by
  apply neg_prefix_tree
  unfold bad
  exact (universalPrefix_rew_iff ψ _).mpr hψ

theorem output_tree (r : ℕ) (ψ : Semiproposition language 7)
    (hψ : UniversalPrefix ψ) (js : List ℕ) : ExistentialTree (output r ψ js) := by
  induction js with
  | nil => exact ExistentialTree.base (by simp [output, Semiformula.Open])
  | cons j js ih => exact ExistentialTree.or (bad_neg_tree r j ψ hψ) ih
end DiophantineConsistency.HerbrandStageExistentialSide
