import DiophantineConsistency.PRAPositiveNormalize
import DiophantineConsistency.ParsonsBasePositive
import DiophantineConsistency.ParsonsHierarchyMap
import DiophantineConsistency.PRAFormulaParameters
/-! Map and pack positive arithmetic formulas without changing their shape. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPositiveMapPack
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRAFormulaParameters PRAPositiveNormalize

theorem mapped {ξ : Type} {n : ℕ} {φ : Semiformula ℒₒᵣ ξ n}
    (h : ParsonsBasePositive.Positive φ) : Positive (Semiformula.lMap embedding φ) := by
  induction h with
  | bounded h => exact .bounded (ParsonsHierarchyMap.hierarchy h)
  | and _ _ ha hb => exact .and ha hb
  | or _ _ ha hb => exact .or ha hb
  | exs _ ha => exact .ex ha

theorem rewrite {ξ η : Type} {n m : ℕ} {φ : Semiformula language ξ n}
    (h : Positive φ) (w : Rew language ξ n η m) : Positive (w ▹ φ) := by
  induction h generalizing η m with
  | bounded h => exact .bounded (Hierarchy.rew _ h)
  | and _ _ ha hb => exact .and (ha w) (hb w)
  | or _ _ ha hb => exact .or (ha w) (hb w)
  | ex _ ha => exact .ex (ha w.q)

theorem toEmpty {ξ : Type} [DecidableEq ξ] {n : ℕ} {φ : Semiformula language ξ n}
    (h : Positive φ) (hf : φ.freeVariables = ∅) : Positive (φ.toEmpty hf) := by
  induction h with
  | @bounded n φ h =>
      apply Positive.bounded
      apply (Hierarchy.rew_iff (ω := (Rew.emb : Rew language Empty _ ξ _))).mp
      rw [Semiformula.emb_toEmpty]
      exact h
  | and _ _ ha hb =>
      rw [Semiformula.toEmpty_and]
      exact Positive.and (ha _) (hb _)
  | or _ _ ha hb =>
      rw [Semiformula.toEmpty_or]
      exact Positive.or (ha _) (hb _)
  | ex _ ha =>
      rw [Semiformula.toEmpty_ex]
      exact Positive.ex (ha _)

theorem packed {n : ℕ} (φ : Semiproposition language n) (h : Positive φ) :
    Positive (packParameters φ) := by
  unfold packParameters
  apply toEmpty
  exact rewrite h _
end DiophantineConsistency.PRAPositiveMapPack
