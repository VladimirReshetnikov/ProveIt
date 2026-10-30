import DiophantineConsistency.HerbrandFourTriplePrenexAdapter
import DiophantineConsistency.HerbrandFixedGoalWeakening
import DiophantineConsistency.PRAStageCodedInduction
import DiophantineConsistency.PRAFourWitnessCodedGoal
set_option autoImplicit false
namespace DiophantineConsistency.PRAOneInductionPremise
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate PRAStageCodedChi
  PRAStageCodedInduction HerbrandFourTriplePrenexAdapter HerbrandFixedGoalWeakening

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]

omit [Nonempty M] in
theorem withoutGoal_eval {m : ℕ} (pred : Code (m+3)) (e : ℕ → M)
    (q w y x y₀ z c v : M) :
    (chiInd pred).Eval ![q,w,y,x,y₀,z,c] e ↔
      (chiMatrix pred).Eval ![q,w,y,x,y₀,z,c,v] e := by
  rw [modelChiInd, modelChiMatrix]

theorem modelPremise {m : ℕ} (pred : Code (m+3)) (θ : Semiproposition language 1)
    (e : ℕ → M) (h : (counterexample pred ⋎ (∃⁰ θ)).Eval ![] e) :
    (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (sourceMatrix (chiMatrix pred) (liftGoal θ))))))))).Eval ![] e := by
  change (counterexample pred).Eval ![] e ∨ (∃⁰ θ).Eval ![] e at h
  simp only [counterexample, Semiformula.eval_ex, Semiformula.eval_all] at h
  simp only [Semiformula.eval_ex, Semiformula.eval_all]
  rcases h with ⟨c,z,y₀,hχ⟩ | ⟨v,hv⟩
  · refine ⟨Classical.choice inferInstance,c,z,y₀,fun x y w => ?_⟩
    obtain ⟨q,hq⟩ := hχ x y w
    change (∃⁰ (chiMatrix pred)).Eval ![w,y,x,y₀,z,c,Classical.choice inferInstance] e ∨
      (liftGoal θ).Eval ![w,y,x,y₀,z,c,Classical.choice inferInstance] e
    left
    rw [Semiformula.eval_ex]
    exact ⟨q,(withoutGoal_eval pred e q w y x y₀ z c (Classical.choice inferInstance)).mp hq⟩
  · let d : M := Classical.choice inferInstance
    refine ⟨v,d,d,d,fun x y w => ?_⟩
    change (∃⁰ (chiMatrix pred)).Eval ![w,y,x,d,d,d,v] e ∨ (liftGoal θ).Eval ![w,y,x,d,d,d,v] e
    right
    exact (goal_eval θ _ e).mpr (by simpa using hv)
end models

/-- A universal-theory proof of the coded induction counterexample-or-goal
sequent supplies the exact four-witness premise. -/
theorem universal_proves_premise {m : ℕ} (pred : Code (m+3)) (θ : Semiproposition language 1)
    (p : UniversalAxiom ⊢ (counterexample pred ⋎ (∃⁰ θ)).univCl) :
    UniversalAxiom ⊢
      (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (sourceMatrix (chiMatrix pred) (liftGoal θ))))))))).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hTheory
  have hp := models_of_provable hTheory p
  simp only [models_iff, Semiformula.eval_univCl] at hp ⊢
  intro e
  exact modelPremise pred θ e (hp e)
/-- The coded induction formula for zero external parameters is independent
of the valuation, because its sole induction parameter is universally bound. -/
theorem closedInduction_eval_independent {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
    (pred : Code (0+3)) (e f : ℕ → M) :
    (inductionFormula pred).Eval ![] e ↔ (inductionFormula pred).Eval ![] f := by
  rw [modelInductionFormula, modelInductionFormula]
  have hp : (fun i : Fin 0 => e i.val) = (fun i : Fin 0 => f i.val) := Subsingleton.elim _ _
  rw [hp]

/-- In the zero-external-parameter case, an actual proof from U plus the
single coded induction axiom yields the counterexample-or-goal U-proof. -/
theorem universal_disjunction_of_one_axiom (pred : Code (0+3)) (θ : Semiproposition language 1)
    (p : (UniversalAxiom ∪ { (inductionFormula pred).univCl }) ⊢ (∃⁰ θ).univCl) :
    UniversalAxiom ⊢ (counterexample pred ⋎ (∃⁰ θ)).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hTheory
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  change (counterexample pred).Eval ![] e ∨ (∃⁰ θ).Eval ![] e
  classical
  by_cases hc : (counterexample pred).Eval ![] e
  · exact Or.inl hc
  · right
    have hI : M↓[language] ⊧ (inductionFormula pred).univCl := by
      simp only [models_iff, Semiformula.eval_univCl]
      intro f
      have he : (inductionFormula pred).Eval ![] e := by
        simpa [inductionFormula, LogicalConnective.HomClass.map_neg] using hc
      exact (closedInduction_eval_independent pred e f).mp he
    have hBoth : M↓[language] ⊧* (UniversalAxiom ∪ { (inductionFormula pred).univCl }) := by
      constructor
      intro σ hσ
      rcases hσ with hU | hIσ
      · exact hTheory.models _ hU
      · simp only [Set.mem_singleton_iff] at hIσ
        subst σ
        exact hI
    have hGoal := models_of_provable hBoth p
    simp only [models_iff, Semiformula.eval_univCl] at hGoal
    exact hGoal e
/-- One closed coded Σ₁-induction axiom can be eliminated from an actual
proof of a universally closed open-matrix existential goal. -/
theorem PRA_proves_goal_of_one_axiom (pred : Code (0+3)) (θ : Semiproposition language 1)
    (hθ : θ.Open)
    (p : (UniversalAxiom ∪ { (inductionFormula pred).univCl }) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  apply PRAFourWitnessCodedGoal.PRA_proves_goal pred θ hθ
  exact universal_proves_premise pred θ (universal_disjunction_of_one_axiom pred θ p)
end DiophantineConsistency.PRAOneInductionPremise
