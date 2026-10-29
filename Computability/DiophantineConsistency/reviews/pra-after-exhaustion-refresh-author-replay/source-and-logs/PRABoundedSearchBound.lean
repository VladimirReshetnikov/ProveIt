import DiophantineConsistency.PRABoundedSearchInvariant
import DiophantineConsistency.PRAPeanoMinusOrderAlgebra

/-! The bounded-search candidate never exceeds its input, in candidate PRA models. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedSearchBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAExhaustion PRAOpenInduction
  PRASelectCode PRABoundedSearchCode PRABoundedSearchInvariant PRAPeanoMinusOrderBasic PRAPeanoMinusOrderAlgebra

private def parameters (n : ℕ) : Fin n → Semiterm language ℕ 1 := fun i => .fvar i.val
private def searchTerm {n : ℕ} (good : Code (n+1)) : Semiterm language ℕ 1 :=
  .func (searchCode good) (Fin.cases (.bvar 0) (parameters n))
private def boundBody {n : ℕ} (good : Code (n+1)) : Semiformula language ℕ 1 :=
  (Semiformula.rel Language.ORing.Rel.lt ![searchTerm good, .bvar 0]) ⋎
    (Semiformula.rel Language.ORing.Rel.eq ![searchTerm good, .bvar 0])

theorem boundBody_open {n : ℕ} (good : Code (n+1)) : (boundBody good).Open := by
  simp [boundBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem boundBody_eval {n : ℕ} (good : Code (n+1)) (x : M) (e : ℕ → M) :
    (boundBody good).Eval ![x] e ↔
      let found := Structure.func (L := language) (searchCode good) (Fin.cases x (fun i : Fin n => e i.val))
      Structure.rel (L := language) Language.ORing.Rel.lt ![found,x] ∨ found = x := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (boundBody good) ↔ _
  dsimp only [boundBody, Semiformula.EvalAux]
  rw [eqRel]
  have hs : (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (parameters n)) =
      Fin.cases x (fun i : Fin n => e i.val) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hp : (Semiterm.val ![x] e ∘ ![(searchTerm good), (.bvar 0 : Semiterm language ℕ 1)]) =
      ![Structure.func (L := language) (searchCode good) (Fin.cases x (fun i : Fin n => e i.val)), x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (searchCode good)
        (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (parameters n)) = _
      rw [hs]
      rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  change (Structure.rel (L := language) Language.ORing.Rel.lt
      (Semiterm.val ![x] e ∘ ![searchTerm good, .bvar 0]) ∨
    (Semiterm.val ![x] e ∘ ![searchTerm good, .bvar 0]) 0 =
      (Semiterm.val ![x] e ∘ ![searchTerm good, .bvar 0]) 1) ↔ _
  rw [hp]
  rfl

private theorem beforeSucc (x : M) :
    Structure.rel (L := language) Language.ORing.Rel.lt
      ![x, Structure.func (L := language) Code.succ (fun _ => x)] := by
  apply (PRAQOrder.modelLtWitness x _).mpr
  refine ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0, ?_⟩
  rw [modelAddSucc, modelAddZero]

theorem modelSearchBound {n : ℕ} (good : Code (n+1)) (x : M) (e : ℕ → M) :
    let found := Structure.func (L := language) (searchCode good) (Fin.cases x (fun i : Fin n => e i.val))
    Structure.rel (L := language) Language.ORing.Rel.lt ![found,x] ∨ found = x := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let params : Fin n → M := fun i => e i.val
  let find : M → M := fun x => Structure.func (L := language) (searchCode good) (Fin.cases x params)
  let g : M → M := fun x => Structure.func (L := language) good (Fin.cases x params)
  apply (boundBody_eval good x e).mp
  apply modelOpenInduction (M := M) (boundBody good) (boundBody_open good) e
  · apply (boundBody_eval good z e).mpr
    change Structure.rel (L := language) Language.ORing.Rel.lt ![find z,z] ∨ find z = z
    exact Or.inr (modelSearchZero good params)
  · intro t ht
    apply (boundBody_eval good (s t) e).mpr
    change Structure.rel (L := language) Language.ORing.Rel.lt ![find (s t),s t] ∨ find (s t) = s t
    have hs := modelSearchStepEquation good (Fin.cases t params)
    change find (s t) = Structure.func (L := language) (searchStep good)
      (Fin.cases t (Fin.cases (find t) params)) at hs
    rw [modelSearchStep] at hs
    change find (s t) = Structure.func (L := language) selectCode ![g (find t),s t,find t] at hs
    by_cases hg : g (find t) = z
    · rw [hg, modelSelectZero] at hs
      rw [hs]
      left
      have hle := (boundBody_eval good t e).mp ht
      change Structure.rel (L := language) Language.ORing.Rel.lt ![find t,t] ∨ find t = t at hle
      rcases hle with hlt | heq
      · exact PRAPeanoMinusOrderAlgebra.modelLtTrans (find t) t (s t) hlt (beforeSucc t)
      · rw [heq]
        exact beforeSucc t
    · have he := (modelZeroOrSuccPred (g (find t))).resolve_left hg
      change s (Structure.func (L := language) predCode (fun _ => g (find t))) = g (find t) at he
      rw [←he, modelSelectSucc] at hs
      exact Or.inr hs

end models
end DiophantineConsistency.PRABoundedSearchBound
