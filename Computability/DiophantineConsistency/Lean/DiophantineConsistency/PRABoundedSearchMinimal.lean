import DiophantineConsistency.PRABoundedSearchInvariant

/-! The predecessor of the bounded-search candidate is good. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedSearchMinimal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion PRAOpenInduction
  PRASelectCode PRABoundedSearchCode PRABoundedSearchInvariant

private def parameters (n : ℕ) : Fin n → Semiterm language ℕ 1 := fun i => .fvar i.val
private def searchTerm {n : ℕ} (good : Code (n+1)) : Semiterm language ℕ 1 :=
  .func (searchCode good) (Fin.cases (.bvar 0) (parameters n))
private def minimalBody {n : ℕ} (good : Code (n+1)) : Semiformula language ℕ 1 :=
  (Semiformula.rel Language.ORing.Rel.eq
    ![searchTerm good, .func (Code.zero 0) Fin.elim0]) ⋎
  (Semiformula.nrel Language.ORing.Rel.eq
    ![.func good (Fin.cases (.func predCode (fun _ => searchTerm good)) (parameters n)),
      .func (Code.zero 0) Fin.elim0])

def minimalSentence {n : ℕ} (good : Code (n+1)) : Sentence language := (∀⁰ minimalBody good).univCl

theorem minimalBody_open {n : ℕ} (good : Code (n+1)) : (minimalBody good).Open := by
  simp [minimalBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem minimalBody_eval {n : ℕ} (good : Code (n+1)) (x : M) (e : ℕ → M) :
    (minimalBody good).Eval ![x] e ↔
    let params := fun i : Fin n => e i.val
    let found := Structure.func (L := language) (searchCode good) (Fin.cases x params)
    found = Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨
      Structure.func (L := language) good (Fin.cases
        (Structure.func (L := language) predCode (fun _ => found)) params) ≠
          Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (minimalBody good) ↔ _
  dsimp only [minimalBody, Semiformula.EvalAux]
  rw [eqRel, eqRel]
  have hz : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hsearch : (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (parameters n)) =
      Fin.cases x (fun i : Fin n => e i.val) := by
    simpa only [Function.comp_def, Semiterm.val_bvar, Semiterm.val_fvar,
      Matrix.cons_val_zero, parameters] using
      val_cases (.bvar 0) (parameters n) ![x] e
  have hgood : (Semiterm.val ![x] e ∘ Fin.cases
      (.func predCode (fun _ => searchTerm good)) (parameters n)) =
      Fin.cases (Structure.func (L := language) predCode (fun _ =>
        Structure.func (L := language) (searchCode good)
          (Fin.cases x (fun i : Fin n => e i.val)))) (fun i : Fin n => e i.val) := by
    have hsearch' : (fun i => Semiterm.val ![x] e (Fin.cases (.bvar 0) (parameters n) i)) =
        Fin.cases x (fun i : Fin n => e i.val) := hsearch
    simpa [Semiterm.val_func, searchTerm, parameters, Function.comp_def, hsearch'] using
      val_cases (.func predCode (fun _ => searchTerm good)) (parameters n) ![x] e
  change (Structure.func (L := language) (searchCode good)
      (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (parameters n)) =
      Structure.func (L := language) (Code.zero 0)
        (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) ∨
    Structure.func (L := language) good (Semiterm.val ![x] e ∘ Fin.cases
      (.func predCode (fun _ => searchTerm good)) (parameters n)) ≠
      Structure.func (L := language) (Code.zero 0)
        (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1))) ↔ _
  rw [hz, hsearch, hgood]

omit [M↓[language] ⊧* PRA] in
theorem minimalSentence_iff {n : ℕ} (good : Code (n+1)) :
    M↓[language] ⊧ minimalSentence good ↔
      ∀ (e : ℕ → M) (x : M),
        let params := fun i : Fin n => e i.val
        let found := Structure.func (L := language) (searchCode good) (Fin.cases x params)
        found = Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨
          Structure.func (L := language) good (Fin.cases
            (Structure.func (L := language) predCode (fun _ => found)) params) ≠
              Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  simp only [models_iff, minimalSentence, Semiformula.eval_univCl, Semiformula.eval_all]
  exact forall_congr' fun e => forall_congr' fun x => minimalBody_eval good x e

theorem modelSearchPredecessorGood {n : ℕ} (good : Code (n+1)) (x : M) (e : ℕ → M) :
    let params := fun i : Fin n => e i.val
    let found := Structure.func (L := language) (searchCode good) (Fin.cases x params)
    found = Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨
      Structure.func (L := language) good (Fin.cases
        (Structure.func (L := language) predCode (fun _ => found)) params) ≠
          Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let p : M → M := fun x => Structure.func (L := language) predCode (fun _ => x)
  let params : Fin n → M := fun i => e i.val
  let find : M → M := fun x => Structure.func (L := language) (searchCode good) (Fin.cases x params)
  let g : M → M := fun x => Structure.func (L := language) good (Fin.cases x params)
  apply (minimalBody_eval good x e).mp
  apply modelOpenInduction (M := M) (minimalBody good) (minimalBody_open good) e
  · apply (minimalBody_eval good z e).mpr
    change find z = z ∨ g (p (find z)) ≠ z
    exact Or.inl (modelSearchZero good params)
  · intro t ht
    apply (minimalBody_eval good (s t) e).mpr
    change find (s t) = z ∨ g (p (find (s t))) ≠ z
    have hs := modelSearchStepEquation good (Fin.cases t params)
    change find (s t) = Structure.func (L := language) (searchStep good)
      (Fin.cases t (Fin.cases (find t) params)) at hs
    rw [modelSearchStep] at hs
    change find (s t) = Structure.func (L := language) selectCode ![g (find t), s t, find t] at hs
    by_cases hg : g (find t) = z
    · rw [hg, modelSelectZero] at hs
      rw [hs]
      exact (minimalBody_eval good t e).mp ht
    · have he := modelZeroOrSuccPred (g (find t))
      have hsucc := he.resolve_left hg
      change s (Structure.func (L := language) predCode (fun _ => g (find t))) = g (find t) at hsucc
      rw [←hsucc, modelSelectSucc] at hs
      right
      rw [hs]
      have hp : p (s t) = t := modelPredSucc t
      rw [hp]
      have hinv := modelSearchCandidateInvariant good t e
      change g (find t) = z ∨ find t = t at hinv
      have htfind := hinv.resolve_left hg
      rw [←htfind]
      exact hg

theorem modelMinimalSentence {n : ℕ} (good : Code (n+1)) : M↓[language] ⊧ minimalSentence good := by
  simp only [models_iff, minimalSentence, Semiformula.eval_univCl, Semiformula.eval_all]
  intro e x
  exact (minimalBody_eval good x e).mpr (modelSearchPredecessorGood good x e)

end models

/-- Candidate PRA proves the universal predecessor-minimality condition for
its fixed-code bounded-search function, with all parameters. -/
theorem PRA_proves_minimalSentence {n : ℕ} (good : Code (n+1)) :
    PRA ⊢ minimalSentence good := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMinimalSentence good

end DiophantineConsistency.PRABoundedSearchMinimal
