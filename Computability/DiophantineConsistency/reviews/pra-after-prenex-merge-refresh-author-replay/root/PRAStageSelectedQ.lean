import DiophantineConsistency.HerbrandPackedContextSemantics
import DiophantineConsistency.PRAChallengePermutation
import DiophantineConsistency.HerbrandChiRetainedStability
import DiophantineConsistency.HerbrandStageBodyEvaluation
/-! Interpret the contextual q selection under a current challenge update. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStageSelectedQ
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAFiniteFunctionCodes PRAChallengePermutation HerbrandStageSupport
  HerbrandTupleSchedule HerbrandChiStageContext HerbrandChiRetainedStability HerbrandStageBodyEvaluation
  HerbrandPackedContextTransfer HerbrandPackedContextSemantics HerbrandFixedGoalWeakening

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelQ_update (r j : ℕ) (q : Code (r+3*j+3)) (e : ℕ → M) (x y w : M) :
    Structure.func (L := language) (challengeFirst q)
      (Fin.cases x (Fin.cases y (Fin.cases w (fun i : Fin (r+3*j) => e i.val)))) =
    Structure.func (L := language) q
      (fun i : Fin (r+3*j+3) => updateChallenges r j e x y w i.val) := by
  rw [modelChallengeFirst]
  congr 1
  funext i
  unfold reorderedIndex updateChallenges
  split
  · rename_i hi
    have h0 : i.val ≠ r+3*j := by omega
    have h1 : i.val ≠ r+3*j+1 := by omega
    have h2 : i.val ≠ r+3*j+2 := by omega
    simp [h0,h1,h2]
  · rename_i hi
    have hge : r+3*j ≤ i.val := by omega
    have hlt : i.val < r+3*j+3 := i.isLt
    have hi0 : i.val = r+3*j ∨ i.val = r+3*j+1 ∨ i.val = r+3*j+2 := by omega
    rcases hi0 with h0 | h1 | h2
    · simp [h0]
    · simp [h1]
      rfl
    · simp [h2]
      rfl
end models
end DiophantineConsistency.PRAStageSelectedQ
