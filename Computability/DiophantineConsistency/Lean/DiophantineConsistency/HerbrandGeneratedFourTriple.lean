import DiophantineConsistency.HerbrandGeneratedSubmodelTriple
import DiophantineConsistency.HerbrandTupleSchedule
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandGeneratedFourTriple
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandGeneratedSubmodel HerbrandTupleSchedule

theorem generated_countermodel {M : Type} [Structure language M] (e : ℕ → M)
    (ψ : Semiproposition language 7) (hψ : UniversalPrefix ψ)
    (hcounter : ∀ t : Tuple, ∃ j k l : ℕ,
      ψ.Eval ![e l, e k, e j, Semiterm.val ![] e (t 3), Semiterm.val ![] e (t 2),
        Semiterm.val ![] e (t 1), Semiterm.val ![] e (t 0)] e) :
    let D := generated (L := language) e
    let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
    ∀ z₀ z₁ z₂ z₃ : D.carrier, ∃ a b c : D.carrier,
      ψ.Eval (s := induced D) ![c,b,a,z₃,z₂,z₁,z₀] e' := by
  dsimp only
  let D := generated (L := language) e
  let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
  intro z₀ z₁ z₂ z₃
  obtain ⟨t₀,ht₀⟩ := z₀.property
  obtain ⟨t₁,ht₁⟩ := z₁.property
  obtain ⟨t₂,ht₂⟩ := z₂.property
  obtain ⟨t₃,ht₃⟩ := z₃.property
  let t : Tuple := ![t₀,t₁,t₂,t₃]
  obtain ⟨j,k,l,hj⟩ := hcounter t
  let a : D.carrier := e' j
  let b : D.carrier := e' k
  let c : D.carrier := e' l
  refine ⟨a,b,c, ?_⟩
  apply universal_down D ψ hψ ![c,b,a,z₃,z₂,z₁,z₀] e'
  have hb : (fun i : Fin 7 => (![c,b,a,z₃,z₂,z₁,z₀] i).val) =
      ![c.val,b.val,a.val,z₃.val,z₂.val,z₁.val,z₀.val] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hf : (fun i => (e' i).val) = e := rfl
  rw [hb,hf]
  simpa [a,b,c,e',t, ← ht₀, ← ht₁, ← ht₂, ← ht₃] using hj

theorem no_countermodel {M : Type} [Structure language M] [Nonempty M]
    (hM : M↓[language] ⊧* UniversalAxiom) (e : ℕ → M)
    (ψ : Semiproposition language 7) (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (∼ψ)))))))).univCl) :
    ¬(∀ t : Tuple, ∃ j k l : ℕ,
      ψ.Eval ![e l, e k, e j, Semiterm.val ![] e (t 3), Semiterm.val ![] e (t 2),
        Semiterm.val ![] e (t 1), Semiterm.val ![] e (t 0)] e) := by
  intro hcounter
  let D := generated (L := language) e
  let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
  letI : Structure language D.carrier := induced D
  letI : Nonempty D.carrier := generated_nonempty e
  have hD : D.carrier↓[language] ⊧* UniversalAxiom := universal_model D (generated_nonempty e) hM
  have hgoal := models_of_provable hD p
  simp only [models_iff, Semiformula.eval_univCl, Semiformula.eval_ex, Semiformula.eval_all,
    LogicalConnective.HomClass.map_neg] at hgoal
  obtain ⟨z₀,z₁,z₂,z₃,hz⟩ := hgoal e'
  obtain ⟨a,b,c,hy⟩ := generated_countermodel e ψ hψ hcounter z₀ z₁ z₂ z₃
  have hnot := hz a b c
  apply hnot
  simpa using hy
end DiophantineConsistency.HerbrandGeneratedFourTriple
