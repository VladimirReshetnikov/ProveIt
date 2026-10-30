import DiophantineConsistency.HerbrandFixedGoalWeakening
import DiophantineConsistency.PRAFormulaParameters
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandFixedGoalExtraction
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandTupleSchedule HerbrandInteractiveFourTriple
  HerbrandFourTriplePrenexAdapter HerbrandFixedGoalWeakening

/-- Extract at a caller-supplied parameter bound. -/
theorem extractAt (r : ℕ) (θ : Semiproposition language 1) (β : Semiproposition language 8)
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

/-- Extraction and fixed-goal weakening from the full four-witness premise,
reserving a common block large enough for both the goal and the matrix. -/
theorem extract (θ : Semiproposition language 1) (β : Semiproposition language 8)
    (hθ : θ.Open) (hβ : β.Open)
    (p : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (sourceMatrix β (liftGoal θ))))))))).univCl) :
    ∃ r n, θ.fvSup ≤ r ∧ β.fvSup ≤ r ∧ (negativePrefix β (liftGoal θ)).fvSup ≤ r ∧
      (UniversalAxiom ⊢ ((∃⁰ θ) ⋎ chiOutput r β (List.range n)).univCl) ∧
      (∀ j k i, (candidate j k).FVar? i → i < r+3*j) := by
  let ψ := negativePrefix β (liftGoal θ)
  let r := max θ.fvSup (max β.fvSup ψ.fvSup)
  obtain ⟨n, hn, hs⟩ := extractAt r θ β hθ hβ p
  exact ⟨r,n, Nat.le_max_left _ _, le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _), hn, hs⟩

end DiophantineConsistency.HerbrandFixedGoalExtraction
