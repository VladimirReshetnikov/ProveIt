import DiophantineConsistency.HerbrandInteractiveFourTriple
/-! Earlier stages are stable when the current challenge variables change. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandStageSupport
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRATheory HerbrandTupleSchedule HerbrandInteractiveFourTriple

section models
variable {M : Type} [Structure language M]

theorem candidate_unchanged (r j : ℕ) (k : Fin 4) (e e' : ℕ → M)
    (he : ∀ i < r+3*j, e i = e' i) :
    Semiterm.val ![] e (candidate j k) = Semiterm.val ![] e' (candidate j k) := by
  apply Semiterm.val_eq_of_funEqOn
  intro i hi
  exact he i (term_support r j k hi)

theorem earlier_bad_unchanged (r i j : ℕ) (ψ : Semiproposition language 7)
    (hψ : ψ.fvSup ≤ r) (hij : i < j) (e e' : ℕ → M)
    (he : ∀ k < r+3*j, e k = e' k) :
    (bad r i ψ).Eval ![] e ↔ (bad r i ψ).Eval ![] e' := by
  apply Semiformula.eval_iff_of_funEqOn
  intro k hk
  apply he k
  have hs := bad_support r i ψ hψ hk
  omega

theorem earlier_output_unchanged (r j : ℕ) (ψ : Semiproposition language 7)
    (hψ : ψ.fvSup ≤ r) (stages : List ℕ) (hStages : ∀ i ∈ stages, i < j)
    (e e' : ℕ → M) (he : ∀ k < r+3*j, e k = e' k) :
    (output r ψ stages).Eval ![] e ↔ (output r ψ stages).Eval ![] e' := by
  rw [output_eval, output_eval]
  exact exists_congr fun i => and_congr_right fun hi =>
    not_congr (earlier_bad_unchanged r i j ψ hψ (hStages i hi) e e' he)
/-- Replace the three challenges at stage j, leaving all earlier indices alone. -/
def updateChallenges (r j : ℕ) (e : ℕ → M) (a b c : M) : ℕ → M :=
  fun i => if i = r+3*j then a else if i = r+3*j+1 then b else
    if i = r+3*j+2 then c else e i

omit [Structure language M] in
theorem updateChallenges_before (r j : ℕ) (e : ℕ → M) (a b c : M) (i : ℕ)
    (hi : i < r+3*j) : updateChallenges r j e a b c i = e i := by
  simp only [updateChallenges]
  have h0 : i ≠ r+3*j := by omega
  have h1 : i ≠ r+3*j+1 := by omega
  have h2 : i ≠ r+3*j+2 := by omega
  simp [h0, h1, h2]

/-- An arbitrary replacement of the current triple preserves the previous
disjunction and each of the four current witness terms. -/
theorem updateChallenges_preserves (r j : ℕ) (ψ : Semiproposition language 7)
    (hψ : ψ.fvSup ≤ r) (e : ℕ → M) (a b c : M) :
    ((output r ψ (List.range j)).Eval ![] e ↔
      (output r ψ (List.range j)).Eval ![] (updateChallenges r j e a b c)) ∧
    ∀ k : Fin 4, Semiterm.val ![] e (candidate j k) =
      Semiterm.val ![] (updateChallenges r j e a b c) (candidate j k) := by
  have he : ∀ i < r+3*j, e i = updateChallenges r j e a b c i := by
    intro i hi
    exact (updateChallenges_before r j e a b c i hi).symm
  refine ⟨earlier_output_unchanged r j ψ hψ (List.range j) ?_ e _ he, ?_⟩
  · intro i hi
    exact List.mem_range.mp hi
  · intro k
    exact candidate_unchanged r j k e _ he
/-- Evaluation after replacing the challenges uses the original four witness
values and original parameter valuation. -/
theorem updated_bad_eval (r j : ℕ) (ψ : Semiproposition language 7)
    (hψ : ψ.fvSup ≤ r) (e : ℕ → M) (a b c : M) :
    (bad r j ψ).Eval ![] (updateChallenges r j e a b c) ↔
      ψ.Eval ![c,b,a, Semiterm.val ![] e (candidate j 3),
        Semiterm.val ![] e (candidate j 2), Semiterm.val ![] e (candidate j 1),
        Semiterm.val ![] e (candidate j 0)] e := by
  have he : ∀ i < r+3*j, e i = updateChallenges r j e a b c i := by
    intro i hi
    exact (updateChallenges_before r j e a b c i hi).symm
  rw [bad_eval]
  have h0 : updateChallenges r j e a b c (r+3*j) = a := by simp [updateChallenges]
  have h1 : updateChallenges r j e a b c (r+3*j+1) = b := by simp [updateChallenges]
  have h2 : updateChallenges r j e a b c (r+3*j+2) = c := by simp [updateChallenges]
  rw [h0,h1,h2]
  rw [←candidate_unchanged r j 0 e _ he, ←candidate_unchanged r j 1 e _ he,
    ←candidate_unchanged r j 2 e _ he, ←candidate_unchanged r j 3 e _ he]
  apply Semiformula.eval_iff_of_funEqOn
  intro i hi
  have hlt := Semiformula.lt_fvSup_of_fvar? hi
  exact (he i (by omega)).symm
/-- A stage can also be removed relative to a goal that already succeeds:
when both the goal and the earlier output fail, the current bad instance is forced by challenge choice. -/
theorem eliminate_last_or_goal (r j : ℕ) (ψ : Semiproposition language 7)
    (hψ : ψ.fvSup ≤ r) (goal : (ℕ → M) → Prop)
    (hFull : ∀ e : ℕ → M, (output r ψ (List.range (j+1))).Eval ![] e)
    (hBad : ∀ e : ℕ → M, ¬goal e → ¬(output r ψ (List.range j)).Eval ![] e → ∃ a b c,
      (bad r j ψ).Eval ![] (updateChallenges r j e a b c)) :
    ∀ e : ℕ → M, (output r ψ (List.range j)).Eval ![] e ∨ goal e := by
  classical
  intro e
  by_cases hg : goal e
  · exact Or.inr hg
  · left
    by_cases hp : (output r ψ (List.range j)).Eval ![] e
    · exact hp
    · obtain ⟨a,b,c,hbad⟩ := hBad e hg hp
      have h := (output_eval r ψ _ _).mp (hFull (updateChallenges r j e a b c))
      obtain ⟨i,hi,hnot⟩ := h
      have hi' := List.mem_range.mp hi
      have hij : i < j := by
        by_contra hn
        have : i = j := by omega
        subst i
        exact hnot hbad
      have hearly : (output r ψ (List.range j)).Eval ![] (updateChallenges r j e a b c) :=
        (output_eval r ψ _ _).mpr ⟨i,List.mem_range.mpr hij,hnot⟩
      exact ((updateChallenges_preserves r j ψ hψ e a b c).1).mpr hearly

/-- One semantic stage can be removed if its current bad instance can be
forced by changing only the current challenge triple. -/
theorem eliminate_last_of_bad (r j : ℕ) (ψ : Semiproposition language 7)
    (hψ : ψ.fvSup ≤ r)
    (hFull : ∀ e : ℕ → M, (output r ψ (List.range (j+1))).Eval ![] e)
    (hBad : ∀ e : ℕ → M, ∃ a b c,
      (bad r j ψ).Eval ![] (updateChallenges r j e a b c)) :
    ∀ e : ℕ → M, (output r ψ (List.range j)).Eval ![] e := by
  simpa using eliminate_last_or_goal r j ψ hψ (fun _ => False) hFull
    (fun e _ _ => hBad e)
end models

/-- A model-uniform challenge construction turns an actual candidate-PRA
staged proof into a closed candidate-PRA proof with the last stage removed,
retaining the goal as a disjunct. The challenge premise is explicit. -/
theorem PRA_proves_eliminateLast_or_goal (r j : ℕ) (ψ : Semiproposition language 7)
    (hψ : ψ.fvSup ≤ r) (goal : Proposition language)
    (hFull : PRA ⊢ (output r ψ (List.range (j+1))).univCl)
    (hBad : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ∀ e : ℕ → M, ¬goal.Eval ![] e →
      ¬(output r ψ (List.range j)).Eval ![] e → ∃ a b c,
        (bad r j ψ).Eval ![] (updateChallenges r j e a b c)) :
    PRA ⊢ ((output r ψ (List.range j)) ⋎ goal).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hh := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hFull
  simp only [models_iff, Semiformula.eval_univCl] at hh ⊢
  intro e
  change (output r ψ (List.range j)).Eval ![] e ∨ goal.Eval ![] e
  exact eliminate_last_or_goal r j ψ hψ (fun e => goal.Eval ![] e) hh (hBad M) e
end DiophantineConsistency.HerbrandStageSupport
