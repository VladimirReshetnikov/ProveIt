import DiophantineConsistency.PRAStageSelectedQ
import DiophantineConsistency.PRAStageTermCompilation
import DiophantineConsistency.PRAStagePredicateExtension
/-! Conditional-selection and coded χ defeat remove one actual stage. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStageCodedRemoval
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAUniversalCandidate PRAUniversalEquivalence PRAFiniteFunctionCodes
  PRAStageCodedChi PRAStagePredicateExtension PRAStageTermCompilation PRAStageSelectedQ PRAChallengePermutation
  HerbrandTupleSchedule HerbrandParameterizedWitness HerbrandFixedGoalWeakening HerbrandChiStageContext
  HerbrandChiRetainedStability HerbrandStageBodyEvaluation HerbrandStageSupport
  HerbrandPackedContextTransfer HerbrandPackedContextSemantics

/-- For the coded Ferreira χ, contextual witness selection and the PR defeat
lemma eliminate one stage in candidate PRA. -/
theorem PRA_proves_removeCodedStage {m : ℕ} (r j : ℕ) (pred : Code (m+3))
    (θ : Semiproposition language 1) (hθ : θ.Open) (hθr : θ.fvSup ≤ r)
    (hβr : (chiMatrix pred).fvSup ≤ r) (hmr : m ≤ r)
    (hFull : PRA ⊢ ((∃⁰ θ) ⋎ chiOutput r (chiMatrix pred) (List.range (j+1))).univCl) :
    PRA ⊢ ((∃⁰ θ) ⋎ chiOutput r (chiMatrix pred) (List.range j)).univCl := by
  have hβ := chiMatrix_open pred
  have hu := universal_proves_candidate hFull
  obtain ⟨q,_,hq⟩ := PRA_select_last r j θ (chiMatrix pred) hθ hβ hθr hβr hu
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  classical
  by_contra hn
  have hside : ¬(((∃⁰ θ) ⋎ chiOutput r (chiMatrix pred) (List.range j)).Eval ![] e) := hn
  let n := r+3*j
  let padded : Code (n+3) := extendPredicate (show m ≤ n by dsimp [n]; omega) pred
  let cCode := parameterCode n (candidate j 1)
  let baseCode := parameterCode n (candidate j 3)
  let stopCode := parameterCode n (candidate j 2)
  let qq : Code (n+3) := challengeFirst q
  obtain ⟨x,y,w,hDefeat⟩ := modelChiDefeat padded cCode baseCode stopCode qq e
    (Semiterm.val ![] e (candidate j 0))
  let e' := updateChallenges r j e x y w
  have hside' : ¬(((∃⁰ θ) ⋎ chiOutput r (chiMatrix pred) (List.range j)).Eval ![] e') := by
    intro hs
    exact hside ((retained_unchanged r j θ (chiMatrix pred) hθr hβr e x y w).mpr hs)
  have hsbound : ((∃⁰ θ) ⋎ chiOutput r (chiMatrix pred) (List.range j)).fvSup ≤ n+3 := by
    have hh := retained_support r j θ (chiMatrix pred) hθr hβr
    dsimp [n]
    omega
  have htbound : (stageBody r j (chiMatrix pred)).fvSup ≤ n+3 := by
    simpa [n] using stageBody_bound r j (chiMatrix pred) hβr
  have hsel := modelSelectedContext ((∃⁰ θ) ⋎ chiOutput r (chiMatrix pred) (List.range j))
    (stageBody r j (chiMatrix pred)) (n+3) hsbound htbound q hq e'
  have hbody := hsel.resolve_left hside'
  have hβeval := (stageBody_updated_eval r j (chiMatrix pred) hβr e
    (Structure.func (L := language) q (fun i : Fin (n+3) => e' i.val)) x y w).mp hbody
  have hqeval := modelQ_update r j q e x y w
  change Structure.func (L := language) qq _ = _ at hqeval
  rw [←hqeval] at hβeval
  have hpadded := (modelExtendedChi (show m ≤ n by dsimp [n]; omega) pred e _ _ _ _ _ _ _ _).mpr hβeval
  apply hDefeat
  simpa only [cCode, baseCode, stopCode, n, modelCandidateCode] using hpadded
/-- Iterating coded stage removal eliminates every finite χ disjunct. -/
theorem PRA_proves_codedGoal_of_stages {m : ℕ} (r n : ℕ) (pred : Code (m+3))
    (θ : Semiproposition language 1) (hθ : θ.Open) (hθr : θ.fvSup ≤ r)
    (hβr : (chiMatrix pred).fvSup ≤ r) (hmr : m ≤ r)
    (hFull : PRA ⊢ ((∃⁰ θ) ⋎ chiOutput r (chiMatrix pred) (List.range n)).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  induction n with
  | zero =>
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hFull
    simp only [models_iff, Semiformula.eval_univCl] at hm ⊢
    intro e
    have he := hm e
    simpa [HerbrandFixedGoalWeakening.chiOutput, Semiformula.Eval] using he
  | succ n ih =>
    apply ih
    exact PRA_proves_removeCodedStage r n pred θ hθ hθr hβr hmr hFull
end DiophantineConsistency.PRAStageCodedRemoval
