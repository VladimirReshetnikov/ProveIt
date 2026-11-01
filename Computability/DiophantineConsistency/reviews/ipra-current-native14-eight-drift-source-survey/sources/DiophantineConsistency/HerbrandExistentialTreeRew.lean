import DiophantineConsistency.HerbrandUniversalTree
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandExistentialTreeRew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage HerbrandUniversalTree

theorem existential_rew {ξ η : Type} {n m : ℕ} {φ : Semiformula language ξ n}
    (h : ExistentialTree φ) (w : Rew language ξ n η m) : ExistentialTree (w ▹ φ) := by
  induction h generalizing η m with
  | base h =>
    apply ExistentialTree.base
    simpa only [Semiformula.Open, PRAFormulaParameters.qr_rew] using h
  | and hp hq ihp ihq => exact ExistentialTree.and (ihp w) (ihq w)
  | or hp hq ihp ihq => exact ExistentialTree.or (ihp w) (ihq w)
  | ex hp ihp => exact ExistentialTree.ex (ihp w.q)
end DiophantineConsistency.HerbrandExistentialTreeRew
