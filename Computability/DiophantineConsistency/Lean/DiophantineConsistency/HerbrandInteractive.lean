import DiophantineConsistency.HerbrandGeneratedSubmodel
import DiophantineConsistency.HerbrandValuationCompact
import DiophantineConsistency.HerbrandSchedule
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandInteractive
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandSchedule HerbrandGeneratedSubmodel HerbrandValuationCompact

/-- Counterexample at a round, with the first r variables reserved for parameters. -/
def bad (r j : ℕ) (ψ : Semiproposition language 2) : Proposition language :=
  Rew.subst ![&(r+j), candidate j] ▹ ψ

theorem bad_eval {M : Type} [Structure language M] (r j : ℕ)
    (ψ : Semiproposition language 2) (e : ℕ → M) :
    (bad r j ψ).Eval ![] e ↔ ψ.Eval ![e (r+j), Semiterm.val ![] e (candidate j)] e := by
  simp [bad, Semiformula.eval_substs]

/-- No input term depends on the current or a later counterexample. -/
theorem term_support (r j : ℕ) {i : ℕ} (h : (candidate j).FVar? i) : i < r+j := by
  have := candidate_before j h
  omega

/-- If ψ's parameters occupy the first r positions, each instantiated
matrix uses no variable beyond the current counterexample position. -/
theorem bad_support (r j : ℕ) (ψ : Semiproposition language 2)
    (hψ : ψ.fvSup ≤ r) {i : ℕ} (h : (bad r j ψ).FVar? i) : i ≤ r+j := by
  unfold bad at h
  rcases Semiformula.fvar?_rew h with (⟨k,hk⟩ | ⟨z,hz,hk⟩)
  · refine Fin.cases ?_ (fun k => ?_) k hk
    · intro hk
      simp [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] at hk
      omega
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
      intro hk
      have hk' : (candidate j).FVar? i := by simpa [Rew.subst_bvar] using hk
      have := term_support r j hk'
      omega
  · have hz' := Semiformula.lt_fvSup_of_fvar? hz
    have hzi : i = z := by
      simpa [Rew.subst_fvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hk
    omega

def failures (r n : ℕ) (ψ : Semiproposition language 2) : Set (Proposition language) :=
  {φ | ∃ j < n, bad r j ψ = φ}

theorem finite_failure (r : ℕ) (ψ : Semiproposition language 2) (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∀⁰ (∼ψ))).univCl) :
    ∃ n, ¬Nonempty (ModelValuation (failures r n ψ)) := by
  classical
  by_contra hn
  push Not at hn
  have hw : ∀ n, Nonempty (ModelValuation ((∅ : Set (Proposition language)) ∪
      {φ | ∃ j < n, bad r j ψ = φ})) := by
    intro n
    simpa only [Set.empty_union, failures] using hn n
  have hW : Nonempty (ModelValuation (Set.range (fun j => bad r j ψ))) := by
    simpa only [Set.empty_union] using valuation_compact_sequence ∅ (fun j => bad r j ψ) hw
  let W := hW.some
  letI : Nonempty W.Carrier := W.nonempty
  letI : Structure language W.Carrier := W.struc
  apply no_countermodel W.models W.valuation ψ hψ p
  intro t
  refine ⟨r + stage t, ?_⟩
  have hh := W.satisfies (bad r (stage t) ψ) ⟨stage t, rfl⟩
  have hh' := (bad_eval r (stage t) ψ W.valuation).mp hh
  simpa [candidate_stage] using hh'
/-- A finite interactive disjunction, with counterexamples at consecutive stages. -/
def output (r : ℕ) (ψ : Semiproposition language 2) : List ℕ → Proposition language
  | [] => ⊥
  | j :: js => ∼(bad r j ψ) ⋎ output r ψ js

theorem output_eval {M : Type} [Structure language M] (r : ℕ)
    (ψ : Semiproposition language 2) (js : List ℕ) (e : ℕ → M) :
    (output r ψ js).Eval ![] e ↔ ∃ j ∈ js, ¬(bad r j ψ).Eval ![] e := by
  induction js with
  | nil => simp [output, Semiformula.Eval]
  | cons j js ih =>
    change ((∼(bad r j ψ)).Eval ![] e ∨ (output r ψ js).Eval ![] e) ↔ _
    rw [LogicalConnective.HomClass.map_neg, ih]
    simp

/-- Actual universal-theory proof of a finite interactive disjunction. Terms at
stage j use variables only before j; the first r positions are reserved for
parameters and the counterexample at round j occupies position r+j. -/
theorem universal_proves_interactive (r : ℕ) (ψ : Semiproposition language 2)
    (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∀⁰ (∼ψ))).univCl) :
    ∃ n, UniversalAxiom ⊢ (output r ψ (List.range n)).univCl := by
  classical
  obtain ⟨n,hn⟩ := finite_failure r ψ hψ p
  refine ⟨n, ?_⟩
  apply proves_univCl_of_no_valuation (failures r n ψ) _ hn
  intro M hM e hbad φ hφ
  obtain ⟨j,hj,rfl⟩ := hφ
  by_contra hjbad
  apply hbad
  exact (output_eval r ψ _ e).mpr ⟨j, List.mem_range.mpr hj, hjbad⟩
/-- Extraction with explicit separation of the parameters of ψ from all
counterexample variables, and the matching term/matrix support guarantees. -/
theorem separated_interactive (ψ : Semiproposition language 2)
    (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∀⁰ (∼ψ))).univCl) :
    ∃ n, (UniversalAxiom ⊢ (output ψ.fvSup ψ (List.range n)).univCl) ∧
      (∀ j i, (candidate j).FVar? i → i < ψ.fvSup+j) ∧
      (∀ j i, (bad ψ.fvSup j ψ).FVar? i → i ≤ ψ.fvSup+j) := by
  obtain ⟨n, hn⟩ := universal_proves_interactive ψ.fvSup ψ hψ p
  exact ⟨n, hn, fun j i h => term_support ψ.fvSup j h,
    fun j i h => bad_support ψ.fvSup j ψ le_rfl h⟩
end DiophantineConsistency.HerbrandInteractive
