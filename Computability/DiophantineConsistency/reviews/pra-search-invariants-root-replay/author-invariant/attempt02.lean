import DiophantineConsistency.PRABoundedSearchCode

/-! An open-induction invariant for parameterized bounded search. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedSearchInvariant
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion PRAOpenInduction
  PRASelectCode PRABoundedSearchCode

private def parameters (n : ℕ) : Fin n → Semiterm language ℕ 1 := fun i => .fvar i.val
private def searchTerm {n : ℕ} (good : Code (n+1)) : Semiterm language ℕ 1 :=
  .func (searchCode good) (Fin.cases (.bvar 0) (parameters n))
private def invariantBody {n : ℕ} (good : Code (n+1)) : Semiformula language ℕ 1 :=
  (Semiformula.rel Language.ORing.Rel.eq
    ![.func good (Fin.cases (searchTerm good) (parameters n)), .func (Code.zero 0) Fin.elim0]) ⋎
  (Semiformula.rel Language.ORing.Rel.eq ![searchTerm good, .bvar 0])

def candidateSentence {n : ℕ} (good : Code (n+1)) : Sentence language := (∀⁰ invariantBody good).univCl

theorem invariantBody_open {n : ℕ} (good : Code (n+1)) : (invariantBody good).Open := by
  simp [invariantBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem invariantBody_eval {n : ℕ} (good : Code (n+1)) (x : M) (e : ℕ → M) :
    (invariantBody good).Eval ![x] e ↔
    let args := Fin.cases x (fun i : Fin n => e i.val)
    let found := Structure.func (L := language) (searchCode good) args
    Structure.func (L := language) good (Fin.cases found (fun i : Fin n => e i.val)) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨ found = x := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (invariantBody good) ↔ _
  dsimp only [invariantBody, Semiformula.EvalAux]
  rw [eqRel, eqRel]
  have hz : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hsearch : (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (parameters n)) =
      Fin.cases x (fun i : Fin n => e i.val) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  have hgood : (Semiterm.val ![x] e ∘ Fin.cases (searchTerm good) (parameters n)) =
      Fin.cases (Structure.func (L := language) (searchCode good)
        (Fin.cases x (fun i : Fin n => e i.val))) (fun i : Fin n => e i.val) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (searchCode good)
        (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (parameters n)) = _
      rw [hsearch]
      rfl
    · rfl
  change (Structure.func (L := language) good
      (Semiterm.val ![x] e ∘ Fin.cases (searchTerm good) (parameters n)) =
      Structure.func (L := language) (Code.zero 0)
        (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) ∨
    Structure.func (L := language) (searchCode good)
      (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (parameters n)) = x) ↔ _
  rw [hgood, hz, hsearch]

theorem modelSearchCandidateInvariant {n : ℕ} (good : Code (n+1)) (x : M) (e : ℕ → M) :
    let params := fun i : Fin n => e i.val
    let found := Structure.func (L := language) (searchCode good) (Fin.cases x params)
    Structure.func (L := language) good (Fin.cases found params) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨ found = x := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let params : Fin n → M := fun i => e i.val
  let find : M → M := fun x => Structure.func (L := language) (searchCode good) (Fin.cases x params)
  let g : M → M := fun x => Structure.func (L := language) good (Fin.cases x params)
  apply (invariantBody_eval good x e).mp
  apply modelOpenInduction (M := M) (invariantBody good) (invariantBody_open good) e
  · apply (invariantBody_eval good z e).mpr
    change g (find z) = z ∨ find z = z
    exact Or.inr (modelSearchZero good params)
  · intro t _
    apply (invariantBody_eval good (s t) e).mpr
    change g (find (s t)) = z ∨ find (s t) = s t
    have hs := modelSearchStepEquation good (Fin.cases t params)
    change find (s t) = Structure.func (L := language) (searchStep good)
      (Fin.cases t (Fin.cases (find t) params)) at hs
    rw [modelSearchStep] at hs
    change find (s t) = Structure.func (L := language) selectCode ![g (find t), s t, find t] at hs
    by_cases hg : g (find t) = z
    · rw [hg, modelSelectZero] at hs
      left
      rw [hs]
      exact hg
    · have hex := modelExhaustion (M := M)
      simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hex
      have he := (PRAExhaustion.body_eval (g (find t)) e).mp (hex e (g (find t)))
      have hp := he.resolve_left hg
      change s (Structure.func (L := language) predCode (fun _ => g (find t))) = g (find t) at hp
      rw [←hp, modelSelectSucc] at hs
      exact Or.inr hs

/-- If the current input is bad, the search output is bad. -/
theorem modelSearchFindsBad {n : ℕ} (good : Code (n+1)) (x : M) (e : ℕ → M)
    (hx : Structure.func (L := language) good (Fin.cases x (fun i : Fin n => e i.val)) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0) :
    Structure.func (L := language) good
      (Fin.cases (Structure.func (L := language) (searchCode good)
        (Fin.cases x (fun i : Fin n => e i.val))) (fun i : Fin n => e i.val)) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  rcases modelSearchCandidateInvariant good x e with h | h
  · exact h
  · rw [h]
    exact hx

theorem modelCandidateSentence {n : ℕ} (good : Code (n+1)) : M↓[language] ⊧ candidateSentence good := by
  simp only [models_iff, candidateSentence, Semiformula.eval_univCl, Semiformula.eval_all]
  intro e x
  exact (invariantBody_eval good x e).mpr (modelSearchCandidateInvariant good x e)

end models

/-- Candidate PRA proves the universal search-candidate invariant for every
fixed predicate code and every parameter vector. -/
theorem PRA_proves_candidateSentence {n : ℕ} (good : Code (n+1)) :
    PRA ⊢ candidateSentence good := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelCandidateSentence good
end DiophantineConsistency.PRABoundedSearchInvariant
