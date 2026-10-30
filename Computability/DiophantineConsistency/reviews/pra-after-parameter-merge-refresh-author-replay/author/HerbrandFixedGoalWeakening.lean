import DiophantineConsistency.HerbrandFourTriplePrenexAdapter
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandFixedGoalWeakening
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalCandidate HerbrandTupleSchedule HerbrandInteractiveFourTriple HerbrandFourTriplePrenexAdapter

/-- The outer witness z₀ is de Bruijn slot 6 after the three challenges and
three further outer witnesses. -/
def liftGoal (θ : Semiproposition language 1) : Semiproposition language 7 :=
  Rew.subst ![#6] ▹ θ

def current (r j : ℕ) (β : Semiproposition language 8) : Proposition language :=
  Rew.subst ![&(r+3*j+2), &(r+3*j+1), &(r+3*j), candidate j 3,
    candidate j 2, candidate j 1, candidate j 0] ▹ (∃⁰ β)

def chiOutput (r : ℕ) (β : Semiproposition language 8) : List ℕ → Proposition language
  | [] => ⊥
  | j :: js => current r j β ⋎ chiOutput r β js

theorem current_eval {M : Type} [Structure language M] (r j : ℕ)
    (β : Semiproposition language 8) (e : ℕ → M) :
    (current r j β).Eval ![] e ↔ (∃⁰ β).Eval
      ![e (r+3*j+2), e (r+3*j+1), e (r+3*j), Semiterm.val ![] e (candidate j 3),
        Semiterm.val ![] e (candidate j 2), Semiterm.val ![] e (candidate j 1),
        Semiterm.val ![] e (candidate j 0)] e := by
  exact HerbrandInteractiveFourTriple.bad_eval r j (∃⁰ β) e

theorem chiOutput_eval {M : Type} [Structure language M] (r : ℕ)
    (β : Semiproposition language 8) (js : List ℕ) (e : ℕ → M) :
    (chiOutput r β js).Eval ![] e ↔ ∃ j ∈ js, (current r j β).Eval ![] e := by
  induction js with
  | nil => simp [chiOutput, Semiformula.Eval]
  | cons j js ih =>
    change ((current r j β).Eval ![] e ∨ (chiOutput r β js).Eval ![] e) ↔ _
    rw [ih]
    simp

theorem goal_eval {M : Type} [Structure language M] (θ : Semiproposition language 1)
    (b : Fin 7 → M) (e : ℕ → M) : (liftGoal θ).Eval b e ↔ θ.Eval ![b 6] e := by
  simp [liftGoal, Semiformula.eval_substs]

/-- Replace each selected goal instance by the same existential goal and
retain only the χ-existentials as staged disjuncts. -/
theorem universal_proves_weakened (r : ℕ) (θ : Semiproposition language 1)
    (β : Semiproposition language 8) (js : List ℕ)
    (p : UniversalAxiom ⊢ (output r (negativePrefix β (liftGoal θ)) js).univCl) :
    UniversalAxiom ⊢ ((∃⁰ θ) ⋎ chiOutput r β js).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hTheory
  have hp := models_of_provable hTheory p
  simp only [models_iff, Semiformula.eval_univCl] at hp ⊢
  intro e
  have hv := hp e
  obtain ⟨j,hj,hjv⟩ := (HerbrandInteractiveFourTriple.output_eval r _ js e).mp hv
  have hjbad := (HerbrandInteractiveFourTriple.bad_eval r j (negativePrefix β (liftGoal θ)) e)
  have hnot : ¬(negativePrefix β (liftGoal θ)).Eval
      ![e (r+3*j+2), e (r+3*j+1), e (r+3*j), Semiterm.val ![] e (candidate j 3),
        Semiterm.val ![] e (candidate j 2), Semiterm.val ![] e (candidate j 1),
        Semiterm.val ![] e (candidate j 0)] e := fun h => hjv (hjbad.mpr h)
  have hsource := (matrix_equiv β (liftGoal θ) _ e).mpr (by simpa using hnot)
  change (∃⁰ θ).Eval ![] e ∨ (chiOutput r β js).Eval ![] e
  change (∃⁰ β).Eval _ e ∨ (liftGoal θ).Eval _ e at hsource
  rcases hsource with hχ | hθ
  · exact Or.inr ((chiOutput_eval r β js e).mpr ⟨j,hj,(current_eval r j β e).mpr hχ⟩)
  · apply Or.inl
    rw [Semiformula.eval_ex]
    refine ⟨Semiterm.val ![] e (candidate j 0), ?_⟩
    simpa using (goal_eval θ _ e).mp hθ
end DiophantineConsistency.HerbrandFixedGoalWeakening
