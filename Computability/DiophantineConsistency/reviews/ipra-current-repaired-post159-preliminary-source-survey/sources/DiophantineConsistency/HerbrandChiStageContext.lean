import DiophantineConsistency.HerbrandFixedGoalWeakening
import DiophantineConsistency.HerbrandExistentialTreeRew
import DiophantineConsistency.PRAProofRewriting
import DiophantineConsistency.HerbrandPackedContextTransfer
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandChiStageContext
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage HerbrandTupleSchedule HerbrandInteractiveFourTriple HerbrandFixedGoalWeakening
  HerbrandUniversalTree HerbrandExistentialTreeRew PRAProofRewriting

/-- The current χ instance as an open formula in the inner witness. -/
def stageBody (r j : ℕ) (β : Semiproposition language 8) : Semiproposition language 1 :=
  (Rew.subst ![&(r+3*j+2), &(r+3*j+1), &(r+3*j), candidate j 3,
    candidate j 2, candidate j 1, candidate j 0]).q ▹ β

theorem current_eq (r j : ℕ) (β : Semiproposition language 8) : current r j β = ∃⁰ stageBody r j β := by
  rfl

theorem stageBody_open (r j : ℕ) (β : Semiproposition language 8) (hβ : β.Open) :
    (stageBody r j β).Open := by
  simpa only [stageBody, Semiformula.rew_open_iff] using hβ

theorem current_tree (r j : ℕ) (β : Semiproposition language 8) (hβ : β.Open) :
    ExistentialTree (current r j β) := by
  rw [current_eq]
  exact ExistentialTree.ex (ExistentialTree.base (stageBody_open r j β hβ))

theorem chiOutput_tree (r : ℕ) (β : Semiproposition language 8) (hβ : β.Open) (js : List ℕ) :
    ExistentialTree (chiOutput r β js) := by
  induction js with
  | nil => exact ExistentialTree.base (by simp [chiOutput, Semiformula.Open])
  | cons j js ih => exact ExistentialTree.or (current_tree r j β hβ) ih

theorem retained_tree (r j : ℕ) (θ : Semiproposition language 1) (β : Semiproposition language 8)
    (hθ : θ.Open) (hβ : β.Open) :
    ExistentialTree ((∃⁰ θ) ⋎ chiOutput r β (List.range j)) :=
  ExistentialTree.or (ExistentialTree.ex (ExistentialTree.base hθ)) (chiOutput_tree r β hβ _)

theorem current_support (r j : ℕ) (β : Semiproposition language 8) (hβ : β.fvSup ≤ r)
    {i : ℕ} (h : (current r j β).FVar? i) : i ≤ r+3*j+2 := by
  have hf : (∃⁰ β).fvSup = β.fvSup := by simp [Semiformula.fvSup]
  apply bad_support r j (∃⁰ β) (by rw [hf]; exact hβ)
  exact h

theorem retained_support (r j : ℕ) (θ : Semiproposition language 1) (β : Semiproposition language 8)
    (hθ : θ.fvSup ≤ r) (hβ : β.fvSup ≤ r) :
    ((∃⁰ θ) ⋎ chiOutput r β (List.range j)).fvSup ≤ r+3*j := by
  apply fvSup_le_of_fvar_lt
  intro i hi
  simp only [Semiformula.fvar?_or, Semiformula.fvar?_exs] at hi
  rcases hi with ht | hc
  · have ht' := Semiformula.lt_fvSup_of_fvar? ht
    omega
  · have hlist : ∀ (js : List ℕ), (∀ k ∈ js, k < j) →
        (chiOutput r β js).FVar? i → i < r+3*j := by
      intro js hjs
      induction js with
      | nil => simp [chiOutput, Semiformula.FVar?]
      | cons k ks ih =>
        simp only [chiOutput, Semiformula.fvar?_or]
        intro hx
        rcases hx with hk | hks
        · have hpos := current_support r k β hβ hk
          have hklt := hjs k (by simp)
          omega
        · apply ih (fun q hq => hjs q (by simp [hq])) hks
    exact hlist (List.range j) (fun k hk => List.mem_range.mp hk) hc
theorem stageBody_bound (r j : ℕ) (β : Semiproposition language 8) (hβ : β.fvSup ≤ r) :
    (stageBody r j β).fvSup ≤ r+3*j+3 := by
  apply fvSup_le_of_fvar_lt
  intro i hi
  have hc : (current r j β).FVar? i := by
    rw [current_eq]
    simpa using hi
  have hi' := current_support r j β hβ hc
  omega

/-- Separate the last χ stage from the retained fixed goal and earlier stages. -/
theorem separate_last (r j : ℕ) (θ : Semiproposition language 1) (β : Semiproposition language 8)
    (p : PRAUniversalCandidate.UniversalAxiom ⊢ ((∃⁰ θ) ⋎ chiOutput r β (List.range (j+1))).univCl) :
    PRAUniversalCandidate.UniversalAxiom ⊢ (((∃⁰ θ) ⋎ chiOutput r β (List.range j)) ⋎ (∃⁰ stageBody r j β)).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hTheory
  have hp := models_of_provable hTheory p
  simp only [models_iff, Semiformula.eval_univCl] at hp ⊢
  intro e
  have hh := hp e
  change (∃⁰ θ).Eval ![] e ∨ (chiOutput r β (List.range (j+1))).Eval ![] e at hh
  change ((∃⁰ θ).Eval ![] e ∨ (chiOutput r β (List.range j)).Eval ![] e) ∨
    (∃⁰ stageBody r j β).Eval ![] e
  rcases hh with hg | hc
  · exact Or.inl (Or.inl hg)
  · obtain ⟨k,hk,hkval⟩ := (chiOutput_eval r β _ e).mp hc
    have hklt := List.mem_range.mp hk
    by_cases hkj : k = j
    · subst k
      exact Or.inr (by simpa only [current_eq] using hkval)
    · have hkltj : k < j := by omega
      exact Or.inl (Or.inr ((chiOutput_eval r β _ e).mpr ⟨k,List.mem_range.mpr hkltj,hkval⟩))

/-- From a proved fixed-goal χ disjunction, select a primitive-recursive
witness for the last stage while retaining the goal and all prior stages. -/
theorem PRA_select_last (r j : ℕ) (θ : Semiproposition language 1) (β : Semiproposition language 8)
    (hθ : θ.Open) (hβ : β.Open) (hθr : θ.fvSup ≤ r) (hβr : β.fvSup ≤ r)
    (p : PRAUniversalCandidate.UniversalAxiom ⊢ ((∃⁰ θ) ⋎ chiOutput r β (List.range (j+1))).univCl) :
    ∃ c : PRAFiniteFunctionCodes.Code (r+3*j+3), Primrec (PRAFiniteFunctionCodes.eval c) ∧
      PRATheory.PRA ⊢ (∀⁰* (HerbrandPackedContextTransfer.packedSide
        ((∃⁰ θ) ⋎ chiOutput r β (List.range j)) (r+3*j+3) (by
          have h := retained_support r j θ β hθr hβr
          omega) ⋎
        PRAHerbrandSelection.openMatrixAt
          (HerbrandPackedContextTransfer.packedMatrix (stageBody r j β) (r+3*j+3)
            (stageBody_bound r j β hβr)) c)) := by
  apply HerbrandPackedContextTransfer.PRA_exists_packedSelection
  · exact retained_tree r j θ β hθ hβ
  · exact stageBody_open r j β hβ
  · exact separate_last r j θ β p
end DiophantineConsistency.HerbrandChiStageContext
