import DiophantineConsistency.PRAUniversalAxiomSyntax
import Foundation.FirstOrder.Ultraproduct
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandValuationCompact
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalCandidate

/-- A model of the candidate universal theory with one valuation satisfying a
specified set of open propositions. -/
structure ModelValuation (S : Set (Proposition language)) where
  Carrier : Type
  nonempty : Nonempty Carrier
  struc : Structure language Carrier
  models : letI := nonempty; letI := struc; Carrier↓[language] ⊧* UniversalAxiom
  valuation : ℕ → Carrier
  satisfies : letI := struc; ∀ φ ∈ S, φ.Evalf valuation

/-- Compactness for a common valuation: finite satisfiability in models of the
candidate universal theory implies simultaneous satisfiability. -/
theorem valuation_compact (S : Set (Proposition language))
    (hfin : ∀ F : Finset (Proposition language), ↑F ⊆ S → Nonempty (ModelValuation (↑F : Set (Proposition language)))) :
    Nonempty (ModelValuation S) := by
  classical
  let I := {F : Finset (Proposition language) // (↑F : Set (Proposition language)) ⊆ S}
  letI : Nonempty I := ⟨⟨∅, by simp⟩⟩
  let cone : Proposition language → Set I := fun φ => {i | φ ∈ i.val}
  have hU : ∃ 𝓤 : Ultrafilter I, Set.image cone S ⊆ 𝓤.sets :=
    Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (by
      haveI : DecidableEq (Set I) := fun _ _ => Classical.propDecidable _
      intro F hF
      have hh : ∃ F' : Finset (Proposition language), (↑F' : Set (Proposition language)) ⊆ S ∧ Finset.image cone F' = F := by
        simpa [Finset.subset_set_image_iff] using hF
      obtain ⟨F',hFS,rfl⟩ := hh
      refine ⟨⟨F',hFS⟩, ?_⟩
      simp [cone])
  obtain ⟨𝓤,h𝓤⟩ := hU
  let W : ∀ i : I, ModelValuation (↑i.val : Set (Proposition language)) :=
    fun i => (hfin i.val i.property).some
  let A : I → Type := fun i => (W i).Carrier
  letI : ∀ i : I, Nonempty (A i) := fun i => (W i).nonempty
  letI : ∀ i : I, Structure language (A i) := fun i => (W i).struc
  let N := Structure.Uprod A 𝓤
  letI : Nonempty N := inferInstance
  letI : Structure language N := inferInstance
  have hN : N↓[language] ⊧* UniversalAxiom := by
    constructor
    intro σ hσ
    apply models_Uprod.mpr
    apply Filter.mem_of_superset (Filter.univ_mem : Set.univ ∈ 𝓤)
    intro i hi
    exact (W i).models.models _ hσ
  let v : ℕ → N := fun x => ⟨fun i => (W i).valuation x⟩
  have hv : ∀ φ ∈ S, φ.Evalf v := by
    intro φ hφ
    apply Semiformula.val_Uprod.mpr
    have hc : cone φ ∈ 𝓤 := h𝓤 ⟨φ,hφ,rfl⟩
    apply Filter.mem_of_superset hc
    intro i hi
    exact (W i).satisfies φ hi
  exact ⟨⟨N, inferInstance, inferInstance, hN, v, hv⟩⟩
/-- Compactness for a fixed side set and a countable family of propositions. -/
theorem valuation_compact_sequence (S : Set (Proposition language))
    (f : ℕ → Proposition language)
    (h : ∀ n, Nonempty (ModelValuation (S ∪ {φ | ∃ j < n, f j = φ}))) :
    Nonempty (ModelValuation (S ∪ Set.range f)) := by
  classical
  let T := Set.range f
  let index : Proposition language → ℕ := fun φ => if h : φ ∈ T then Classical.choose h else 0
  have hindex : ∀ φ ∈ T, f (index φ) = φ := by
    intro φ hφ
    simp only [index, dif_pos hφ]
    exact Classical.choose_spec hφ
  apply valuation_compact
  intro F hF
  let n := F.sup index + 1
  let W := (h n).some
  have hsub : (↑F : Set (Proposition language)) ⊆ S ∪ {φ | ∃ j < n, f j = φ} := by
    intro φ hφ
    rcases hF hφ with hs | ht
    · exact Or.inl hs
    · right
      refine ⟨index φ, ?_, hindex φ ht⟩
      have := Finset.le_sup (f := index) hφ
      dsimp [n]
      omega
  exact ⟨⟨W.Carrier, W.nonempty, W.struc, W.models, W.valuation,
    fun φ hφ => W.satisfies φ (hsub hφ)⟩⟩
/-- Prove a universally closed proposition when its failure would satisfy an
inconsistent family of open propositions. -/
theorem proves_univCl_of_no_valuation (S : Set (Proposition language))
    (φ : Proposition language) (hn : ¬Nonempty (ModelValuation S))
    (hbad : ∀ {M : Type} [Structure language M] (e : ℕ → M),
      ¬φ.Eval ![] e → ∀ ψ ∈ S, ψ.Eval ![] e) :
    UniversalAxiom ⊢ φ.univCl := by
  classical
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hTheory
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  by_contra h
  exact hn ⟨⟨M, hM0, hM, hTheory, e, hbad e h⟩⟩
/-- A recursively formed finite disjunction holds exactly when one of its
listed disjuncts holds. -/
theorem eval_list_disjunction {M : Type} [Structure language M] {α : Type}
    (item : α → Proposition language) (out : List α → Proposition language)
    (hnil : out [] = ⊥) (hcons : ∀ a as, out (a :: as) = item a ⋎ out as)
    (xs : List α) (e : ℕ → M) :
    (out xs).Eval ![] e ↔ ∃ a ∈ xs, (item a).Eval ![] e := by
  induction xs with
  | nil => rw [hnil]; simp [Semiformula.Eval]
  | cons a as ih =>
    rw [hcons]
    change ((item a).Eval ![] e ∨ (out as).Eval ![] e) ↔ _
    rw [ih]
    simp
end DiophantineConsistency.HerbrandValuationCompact
