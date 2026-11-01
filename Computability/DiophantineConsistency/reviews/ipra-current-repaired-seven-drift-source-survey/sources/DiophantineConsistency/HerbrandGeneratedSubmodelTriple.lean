import DiophantineConsistency.HerbrandGeneratedSubmodel
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandGeneratedSubmodelTriple
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandGeneratedSubmodel

theorem generated_countermodel_triple {M : Type} [Structure language M] (e : ℕ → M)
    (ψ : Semiproposition language 4) (hψ : UniversalPrefix ψ)
    (hcounter : ∀ t : SyntacticTerm language, ∃ j k l : ℕ,
      ψ.Eval ![e l, e k, e j, Semiterm.val ![] e t] e) :
    let D := generated (L := language) e
    let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
    ∀ x : D.carrier, ∃ a b c : D.carrier, ψ.Eval (s := induced D) ![c,b,a,x] e' := by
  dsimp only
  let D := generated (L := language) e
  let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
  intro x
  obtain ⟨t,ht⟩ := x.property
  obtain ⟨j,k,l,hj⟩ := hcounter t
  let a : D.carrier := e' j
  let b : D.carrier := e' k
  let c : D.carrier := e' l
  refine ⟨a,b,c, ?_⟩
  apply universal_down D ψ hψ ![c,b,a,x] e'
  have hb : (fun i : Fin 4 => (![c,b,a,x] i).val) = ![c.val,b.val,a.val,x.val] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hf : (fun i => (e' i).val) = e := rfl
  rw [hb,hf]
  simpa [a,b,c,e', ← ht] using hj

theorem no_triple_countermodel {M : Type} [Structure language M] [Nonempty M]
    (hM : M↓[language] ⊧* UniversalAxiom) (e : ℕ → M)
    (ψ : Semiproposition language 4) (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (∼ψ))))).univCl) :
    ¬(∀ t : SyntacticTerm language, ∃ j k l : ℕ,
      ψ.Eval ![e l, e k, e j, Semiterm.val ![] e t] e) := by
  intro hcounter
  let D := generated (L := language) e
  let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
  letI : Structure language D.carrier := induced D
  letI : Nonempty D.carrier := generated_nonempty e
  have hD : D.carrier↓[language] ⊧* UniversalAxiom := universal_model D (generated_nonempty e) hM
  have hgoal := models_of_provable hD p
  simp only [models_iff, Semiformula.eval_univCl, Semiformula.eval_ex, Semiformula.eval_all,
    LogicalConnective.HomClass.map_neg] at hgoal
  obtain ⟨x,hx⟩ := hgoal e'
  obtain ⟨a,b,c,hy⟩ := generated_countermodel_triple e ψ hψ hcounter x
  have hnot := hx a b c
  apply hnot
  simpa using hy
end DiophantineConsistency.HerbrandGeneratedSubmodelTriple
