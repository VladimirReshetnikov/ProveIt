import DiophantineConsistency.HerbrandChiStageContext
import DiophantineConsistency.HerbrandStageSupport
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandChiRetainedStability
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage HerbrandFixedGoalWeakening HerbrandChiStageContext HerbrandStageSupport

/-- The fixed goal and all earlier χ stages are unchanged by replacing the
current challenge triple. -/
theorem retained_unchanged {M : Type} [Structure language M]
    (r j : ℕ) (θ : Semiproposition language 1) (β : Semiproposition language 8)
    (hθ : θ.fvSup ≤ r) (hβ : β.fvSup ≤ r) (e : ℕ → M) (a b c : M) :
    (((∃⁰ θ) ⋎ chiOutput r β (List.range j)).Eval ![] e) ↔
      (((∃⁰ θ) ⋎ chiOutput r β (List.range j)).Eval ![] (updateChallenges r j e a b c)) := by
  apply Semiformula.eval_iff_of_funEqOn
  intro i hi
  have h := Semiformula.lt_fvSup_of_fvar? hi
  have hb := retained_support r j θ β hθ hβ
  exact (updateChallenges_before r j e a b c i (by omega)).symm
end DiophantineConsistency.HerbrandChiRetainedStability
