import DiophantineConsistency.HerbrandGeneratedFourTriple
import DiophantineConsistency.HerbrandValuationCompact
import DiophantineConsistency.HerbrandTupleSchedule
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandInteractiveFourTriple
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandTupleSchedule HerbrandGeneratedFourTriple HerbrandValuationCompact

/-- Counterexample at a round, with the first r variables reserved for parameters. -/
def bad (r j : ℕ) (ψ : Semiproposition language 7) : Proposition language :=
  Rew.subst ![&(r+3*j+2), &(r+3*j+1), &(r+3*j), candidate j 3, candidate j 2, candidate j 1, candidate j 0] ▹ ψ

theorem bad_eval {M : Type} [Structure language M] (r j : ℕ)
    (ψ : Semiproposition language 7) (e : ℕ → M) :
    (bad r j ψ).Eval ![] e ↔ ψ.Eval ![e (r+3*j+2), e (r+3*j+1), e (r+3*j), Semiterm.val ![] e (candidate j 3), Semiterm.val ![] e (candidate j 2), Semiterm.val ![] e (candidate j 1), Semiterm.val ![] e (candidate j 0)] e := by
  have he : (Semiterm.val ![] e ∘ ![&(r+3*j+2), &(r+3*j+1), &(r+3*j),
      candidate j 3, candidate j 2, candidate j 1, candidate j 0]) =
      ![e (r+3*j+2), e (r+3*j+1), e (r+3*j), Semiterm.val ![] e (candidate j 3),
        Semiterm.val ![] e (candidate j 2), Semiterm.val ![] e (candidate j 1), Semiterm.val ![] e (candidate j 0)] := by
    funext k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  simp only [bad, Semiformula.eval_substs]
  rw [he]

/-- No input tuple term depends on the current or a later counterexample. -/
theorem term_support (r j : ℕ) (k : Fin 4) {i : ℕ} (h : (candidate j k).FVar? i) : i < r+3*j := by
  have := candidate_before j k h
  omega

/-- If ψ's parameters occupy the first r positions, each instantiated
matrix uses no variable beyond the current counterexample position. -/
theorem bad_support (r j : ℕ) (ψ : Semiproposition language 7)
    (hψ : ψ.fvSup ≤ r) {i : ℕ} (h : (bad r j ψ).FVar? i) : i ≤ r+3*j+2 := by
  unfold bad at h
  rcases Semiformula.fvar?_rew h with (⟨k,hk⟩ | ⟨z,hz,hk⟩)
  · refine Fin.cases ?_ (fun k => ?_) k hk
    · intro hk
      simp [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] at hk
      omega
    · refine Fin.cases ?_ (fun k => ?_) k
      · intro hk
        simp [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] at hk
        omega
      · refine Fin.cases ?_ (fun k => ?_) k
        · intro hk
          simp [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] at hk
          omega
        · refine Fin.cases ?_ (fun k => ?_) k
          · intro hk
            have hk' : (candidate j 3).FVar? i := by simpa [Rew.subst_bvar] using hk
            have := term_support r j 3 hk'
            omega
          · refine Fin.cases ?_ (fun k => ?_) k
            · intro hk
              have hk' : (candidate j 2).FVar? i := by simpa [Rew.subst_bvar] using hk
              have := term_support r j 2 hk'
              omega
            · refine Fin.cases ?_ (fun k => ?_) k
              · intro hk
                have hk' : (candidate j 1).FVar? i := by simpa [Rew.subst_bvar] using hk
                have := term_support r j 1 hk'
                omega
              · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
                · intro hk
                  have hk' : (candidate j 0).FVar? i := by simpa [Rew.subst_bvar] using hk
                  have := term_support r j 0 hk'
                  omega
  · have hz' := Semiformula.lt_fvSup_of_fvar? hz
    have hzi : i = z := by
      simpa [Rew.subst_fvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hk
    omega

def failures (r n : ℕ) (ψ : Semiproposition language 7) : Set (Proposition language) :=
  {φ | ∃ j < n, bad r j ψ = φ}

theorem finite_failure (r : ℕ) (ψ : Semiproposition language 7) (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (∼ψ)))))))).univCl) :
    ∃ n, ¬Nonempty (ModelValuation (failures r n ψ)) := by
  classical
  by_contra hn
  push Not at hn
  let S : Set (Proposition language) := Set.range (fun j => bad r j ψ)
  let index : Proposition language → ℕ := fun φ => if h : φ ∈ S then Classical.choose h else 0
  have hindex : ∀ φ ∈ S, bad r (index φ) ψ = φ := by
    intro φ hφ
    simp only [index, dif_pos hφ]
    exact Classical.choose_spec hφ
  have hfin : ∀ F : Finset (Proposition language), (↑F : Set (Proposition language)) ⊆ S →
      Nonempty (ModelValuation (↑F : Set (Proposition language))) := by
    intro F hF
    let n := F.sup index + 1
    let W := (hn n).some
    have hsub : (↑F : Set (Proposition language)) ⊆ failures r n ψ := by
      intro φ hφ
      refine ⟨index φ, ?_, hindex φ (hF hφ)⟩
      have := Finset.le_sup (f := index) hφ
      dsimp [n]
      omega
    exact ⟨⟨W.Carrier, W.nonempty, W.struc, W.models, W.valuation,
      fun φ hφ => W.satisfies φ (hsub hφ)⟩⟩
  let W := (valuation_compact S hfin).some
  letI : Nonempty W.Carrier := W.nonempty
  letI : Structure language W.Carrier := W.struc
  apply no_countermodel W.models W.valuation ψ hψ p
  intro t
  refine ⟨r + 3*stage t, r + 3*stage t + 1, r + 3*stage t + 2, ?_⟩
  have hh := W.satisfies (bad r (stage t) ψ) ⟨stage t, rfl⟩
  have hh' := (bad_eval r (stage t) ψ W.valuation).mp hh
  simpa [candidate_stage] using hh'
/-- A finite interactive disjunction, with counterexamples at consecutive stages. -/
def output (r : ℕ) (ψ : Semiproposition language 7) : List ℕ → Proposition language
  | [] => ⊥
  | j :: js => ∼(bad r j ψ) ⋎ output r ψ js

theorem output_eval {M : Type} [Structure language M] (r : ℕ)
    (ψ : Semiproposition language 7) (js : List ℕ) (e : ℕ → M) :
    (output r ψ js).Eval ![] e ↔ ∃ j ∈ js, ¬(bad r j ψ).Eval ![] e := by
  induction js with
  | nil => simp [output, Semiformula.Eval]
  | cons j js ih =>
    change ((∼(bad r j ψ)).Eval ![] e ∨ (output r ψ js).Eval ![] e) ↔ _
    rw [LogicalConnective.HomClass.map_neg, ih]
    simp

/-- Actual universal-theory proof of a finite interactive disjunction. All four terms at
stage j use variables only before j; the first r positions are reserved for
parameters and the three counterexamples at round j occupy positions r+3j through r+3j+2. -/
theorem universal_proves_interactive (r : ℕ) (ψ : Semiproposition language 7)
    (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (∼ψ)))))))).univCl) :
    ∃ n, UniversalAxiom ⊢ (output r ψ (List.range n)).univCl := by
  classical
  obtain ⟨n,hn⟩ := finite_failure r ψ hψ p
  refine ⟨n, ?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hTheory
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  apply (output_eval r ψ _ e).mpr
  by_contra h
  have hbad : ∀ j < n, (bad r j ψ).Eval ![] e := by
    intro j hj
    by_contra hjbad
    apply h
    exact ⟨j, List.mem_range.mpr hj, hjbad⟩
  apply hn
  refine ⟨⟨M, hM0, hM, hTheory, e, ?_⟩⟩
  intro φ hφ
  obtain ⟨j,hj,rfl⟩ := hφ
  exact hbad j hj
/-- Extraction with explicit separation of the parameters of ψ from all
counterexample variables, and the matching term/matrix support guarantees. -/
theorem separated_interactive (ψ : Semiproposition language 7)
    (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (∼ψ)))))))).univCl) :
    ∃ n, (UniversalAxiom ⊢ (output ψ.fvSup ψ (List.range n)).univCl) ∧
      (∀ j k i, (candidate j k).FVar? i → i < ψ.fvSup+3*j) ∧
      (∀ j i, (bad ψ.fvSup j ψ).FVar? i → i ≤ ψ.fvSup+3*j+2) := by
  obtain ⟨n, hn⟩ := universal_proves_interactive ψ.fvSup ψ hψ p
  exact ⟨n, hn, fun j k i h => term_support ψ.fvSup j k h,
    fun j i h => bad_support ψ.fvSup j ψ le_rfl h⟩
end DiophantineConsistency.HerbrandInteractiveFourTriple
