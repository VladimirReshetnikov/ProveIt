import DiophantineConsistency.HerbrandUniversalTree
import DiophantineConsistency.HerbrandValuationCompact
import DiophantineConsistency.HerbrandSchedule
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandContextualTreeWitness
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandSchedule HerbrandGeneratedSubmodel HerbrandUniversalTree HerbrandValuationCompact

/-- A universal side condition survives in the term-generated model, where
failure of every term instance contradicts the asserted existential. -/
theorem no_contextual_countermodel {M : Type} [Structure language M] [Nonempty M]
    (hM : M↓[language] ⊧* UniversalAxiom) (e : ℕ → M)
    (side : Proposition language) (hs : UniversalTree side)
    (θ : Semiproposition language 1) (ht : θ.Open)
    (p : UniversalAxiom ⊢ ((∼side) ⋎ (∃⁰ θ)).univCl) :
    ¬(side.Eval ![] e ∧ ∀ t : SyntacticTerm language, ¬(θ/[t]).Eval ![] e) := by
  rintro ⟨hside,hcounter⟩
  let D := generated (L := language) e
  let e' : ℕ → D.carrier := fun i => ⟨e i, generated_contains e i⟩
  letI : Structure language D.carrier := induced D
  letI : Nonempty D.carrier := generated_nonempty e
  have hD : D.carrier↓[language] ⊧* UniversalAxiom := universal_model D (generated_nonempty e) hM
  have hsideD : side.Eval (s := induced D) ![] e' := by
    apply HerbrandUniversalTree.down D side hs ![] e'
    have hb : (fun i : Fin 0 => ((![] : Fin 0 → D.carrier) i).val) = ![] := Subsingleton.elim _ _
    have hf : (fun i => (e' i).val) = e := rfl
    rw [hb,hf]
    exact hside
  have hgoal := models_of_provable hD p
  simp only [models_iff, Semiformula.eval_univCl] at hgoal
  have hg := hgoal e'
  change ((∼side).Eval ![] e' ∨ (∃⁰ θ).Eval ![] e') at hg
  rw [LogicalConnective.HomClass.map_neg, Semiformula.eval_ex] at hg
  rcases hg with hnot | ⟨z,hz⟩
  · exact hnot hsideD
  · obtain ⟨t,htval⟩ := z.property
    apply hcounter t
    have hz' := (eval_open D θ ht ![z] e').mp hz
    have hb : (fun i : Fin 1 => (![z] i).val) = ![z.val] := by
      funext i
      exact Fin.cases rfl (fun i => Fin.elim0 i) i
    have hf : (fun i => (e' i).val) = e := rfl
    rw [hb,hf] at hz'
    simpa [Semiformula.eval_substs, ← htval] using hz'
def absent (θ : Semiproposition language 1) (j : ℕ) : Proposition language :=
  ∼(θ/[candidate j])

def failures (side : Proposition language) (θ : Semiproposition language 1) (n : ℕ) : Set (Proposition language) :=
  {φ | φ = side ∨ ∃ j < n, absent θ j = φ}

theorem finite_failure (side : Proposition language) (hs : UniversalTree side)
    (θ : Semiproposition language 1) (ht : θ.Open)
    (p : UniversalAxiom ⊢ ((∼side) ⋎ (∃⁰ θ)).univCl) :
    ∃ n, ¬Nonempty (ModelValuation (failures side θ n)) := by
  classical
  by_contra hn
  push Not at hn
  let T : Set (Proposition language) := Set.range (absent θ)
  let S : Set (Proposition language) := {side} ∪ T
  let index : Proposition language → ℕ := fun φ => if h : φ ∈ T then Classical.choose h else 0
  have hindex : ∀ φ ∈ T, absent θ (index φ) = φ := by
    intro φ hφ
    simp only [index, dif_pos hφ]
    exact Classical.choose_spec hφ
  have hfin : ∀ F : Finset (Proposition language), (↑F : Set (Proposition language)) ⊆ S →
      Nonempty (ModelValuation (↑F : Set (Proposition language))) := by
    intro F hF
    let n := F.sup index + 1
    let W := (hn n).some
    have hsub : (↑F : Set (Proposition language)) ⊆ failures side θ n := by
      intro φ hφ
      have hf := hF hφ
      rcases hf with h | h
      · left
        exact h
      · right
        refine ⟨index φ, ?_, hindex φ h⟩
        have := Finset.le_sup (f := index) hφ
        dsimp [n]
        omega
    exact ⟨⟨W.Carrier, W.nonempty, W.struc, W.models, W.valuation,
      fun φ hφ => W.satisfies φ (hsub hφ)⟩⟩
  let W := (valuation_compact S hfin).some
  letI : Nonempty W.Carrier := W.nonempty
  letI : Structure language W.Carrier := W.struc
  apply no_contextual_countermodel W.models W.valuation side hs θ ht p
  refine ⟨W.satisfies side (Or.inl rfl), ?_⟩
  intro t
  have hh := W.satisfies (absent θ (stage t)) (Or.inr ⟨stage t,rfl⟩)
  simpa [absent, candidate_stage, LogicalConnective.HomClass.map_neg] using hh
def termOutput (θ : Semiproposition language 1) : List ℕ → Proposition language
  | [] => ⊥
  | j :: js => (θ/[candidate j]) ⋎ termOutput θ js

theorem output_eval {M : Type} [Structure language M] (θ : Semiproposition language 1)
    (js : List ℕ) (e : ℕ → M) :
    (termOutput θ js).Eval ![] e ↔ ∃ j ∈ js, (θ/[candidate j]).Eval ![] e := by
  induction js with
  | nil => simp [termOutput, Semiformula.Eval]
  | cons j js ih =>
    change ((θ/[candidate j]).Eval ![] e ∨ (termOutput θ js).Eval ![] e) ↔ _
    rw [ih]
    simp

/-- Finite contextual Herbrand extraction, retaining an existential side
formula `∼side` rather than assuming it false globally. -/
theorem universal_proves_contextual (side : Proposition language) (hs : UniversalTree side)
    (θ : Semiproposition language 1) (ht : θ.Open)
    (p : UniversalAxiom ⊢ ((∼side) ⋎ (∃⁰ θ)).univCl) :
    ∃ n, UniversalAxiom ⊢ ((∼side) ⋎ termOutput θ (List.range n)).univCl := by
  classical
  obtain ⟨n,hn⟩ := finite_failure side hs θ ht p
  refine ⟨n, ?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hTheory
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  change ((∼side).Eval ![] e ∨ (termOutput θ (List.range n)).Eval ![] e)
  rw [LogicalConnective.HomClass.map_neg, output_eval]
  by_contra h
  have hside : side.Eval ![] e := by
    by_contra hs
    exact h (Or.inl hs)
  have hbad : ∀ j < n, (absent θ j).Eval ![] e := by
    intro j hj
    simp only [absent, LogicalConnective.HomClass.map_neg]
    intro hjt
    apply h
    exact Or.inr ⟨j, List.mem_range.mpr hj, hjt⟩
  apply hn
  refine ⟨⟨M, hM0, hM, hTheory, e, ?_⟩⟩
  intro φ hφ
  rcases hφ with rfl | ⟨j,hj,rfl⟩
  · exact hside
  · exact hbad j hj
end DiophantineConsistency.HerbrandContextualTreeWitness
