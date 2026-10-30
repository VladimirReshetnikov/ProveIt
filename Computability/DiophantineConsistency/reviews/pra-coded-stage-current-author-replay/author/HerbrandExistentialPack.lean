import DiophantineConsistency.HerbrandExistentialTreeRew
import DiophantineConsistency.PRAFormulaParameters
import DiophantineConsistency.HerbrandStageExistentialSide
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandExistentialPack
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAFormulaParameters HerbrandUniversalTree HerbrandExistentialTreeRew

theorem toEmpty_tree {ξ : Type} [DecidableEq ξ] {n : ℕ} {φ : Semiformula language ξ n}
    (h : ExistentialTree φ) (hf : φ.freeVariables = ∅) : ExistentialTree (φ.toEmpty hf) := by
  induction h with
  | @base k φ h =>
    apply ExistentialTree.base
    have hqr : ((Rewriting.emb (φ.toEmpty hf) : Semiformula language ξ _)).qr = φ.qr := by
      rw [Semiformula.emb_toEmpty]
    rw [PRAFormulaParameters.qr_rew] at hqr
    change (φ.toEmpty hf).qr = 0
    rw [hqr]
    exact h
  | and hp hq ihp ihq =>
    rw [Semiformula.toEmpty_and]
    apply ExistentialTree.and
    · apply ihp
    · apply ihq
  | or hp hq ihp ihq =>
    rw [Semiformula.toEmpty_or]
    apply ExistentialTree.or
    · apply ihp
    · apply ihq
  | ex hp ihp =>
    rw [Semiformula.toEmpty_ex]
    apply ExistentialTree.ex
    apply ihp

theorem pack_tree {n : ℕ} (φ : Semiproposition language n) (h : ExistentialTree φ) :
    ExistentialTree (packParameters φ) := by
  unfold packParameters
  apply toEmpty_tree
  exact existential_rew h _
theorem stage_output_pack (r : ℕ) (ψ : Semiproposition language 7)
    (hψ : PRAUniversalSyntax.UniversalPrefix ψ) (js : List ℕ) :
    ExistentialTree (packParameters (HerbrandInteractiveFourTriple.output r ψ js)) :=
  pack_tree _ (HerbrandStageExistentialSide.output_tree r ψ hψ js)
end DiophantineConsistency.HerbrandExistentialPack
