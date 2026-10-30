import DiophantineConsistency.HerbrandFixedGoalExtraction
/-! Fixed-goal extraction with a caller-supplied parameter block. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandFixedGoalExtractionBound
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandTupleSchedule HerbrandInteractiveFourTriple
  HerbrandFourTriplePrenexAdapter HerbrandFixedGoalWeakening

/-- Any explicit bound may reserve extra parameters, e.g. those needed by a
coded predicate, while preserving all actual staged proof and support data. -/
theorem extractBound (r : ℕ) (θ : Semiproposition language 1) (β : Semiproposition language 8)
    (hθ : θ.Open) (hβ : β.Open)
    (p : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (sourceMatrix β (liftGoal θ))))))))).univCl) :
    ∃ n, (UniversalAxiom ⊢ ((∃⁰ θ) ⋎ chiOutput r β (List.range n)).univCl) ∧
      (∀ j k i, (candidate j k).FVar? i → i < r+3*j) := by
  let ψ := negativePrefix β (liftGoal θ)
  have hgoal : (liftGoal θ).Open := by
    change (liftGoal θ).qr = 0
    unfold liftGoal
    rw [PRAFormulaParameters.qr_rew]
    exact hθ
  have hψ : UniversalPrefix ψ := prefix_normalized β (liftGoal θ) hβ hgoal
  have pp : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (∼ψ)))))))).univCl :=
    normalize_proof β (liftGoal θ) p
  obtain ⟨n,hn⟩ := universal_proves_interactive r ψ hψ pp
  refine ⟨n, universal_proves_weakened r θ β (List.range n) hn, ?_⟩
  intro j k i hi
  exact term_support r j k hi
end DiophantineConsistency.HerbrandFixedGoalExtractionBound
