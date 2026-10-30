import DiophantineConsistency.PRAPositiveRuleSemantics
/-! Positive induction is an admissible rule of candidate PRA. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAPositiveAdmissible
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation
  PRAJoostenWitnessedRule HerbrandParameterizedWitness HerbrandContextualTreeSelection
  ParsonsRule ParsonsPositiveComparison PRAPositiveCode PRAPositiveRuleSemantics

theorem admissible : PositiveAdmissible := by
  intro φ hφ hbase hstep
  obtain ⟨pred,hcode⟩ := positive_has_code φ hφ
  let n := (Semiformula.lMap embedding φ).fvSup
  have hpbase : PRA ⊢ (∀⁰* ∃⁰ baseMatrix pred) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    have hb := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbase
    simp only [models_iff, Semiformula.eval_univCl] at hb
    simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex]
    intro v
    let e : ℕ → M := parameterEnv n v
    have hφzero := (modelMappedBase φ e).mp (hb e)
    obtain ⟨y,hy⟩ := (hcode M _ e).mp hφzero
    refine ⟨y, (modelBaseMatrix pred y v).mpr ?_⟩
    have hv : (fun i : Fin n => e i.val) = v := by
      funext i
      simp [e,parameterEnv,i.isLt]
    rw [hv] at hy
    exact hy
  have hpstep : PRA ⊢ ((parameterSide (stepSide pred)) ⋎
      (∃⁰ (parameterMatrix (stepMatrix pred)))).univCl := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    have hs := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hstep
    simp only [models_iff, Semiformula.eval_univCl] at hs ⊢
    intro e
    let v : Fin (n+2) → M := fun i => e i.val
    let x : M := e 0
    let y : M := e 1
    let ep : ℕ → M := fun i => e (i+2)
    have hv : Fin.cases x (Fin.cases y (fun i : Fin n => ep i.val)) = v := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      refine Fin.cases rfl (fun k => ?_) j
      simp [v,ep]
    classical
    by_cases hxy : Structure.func (L := language) pred v = Structure.func (L := language) oneCode Fin.elim0
    · have hp : (Semiformula.lMap embedding φ).Eval ![x] ep := by
        apply (hcode M x ep).mpr
        refine ⟨y, ?_⟩
        rw [hv]
        exact hxy
      have hnext := (modelMappedStep φ ep).mp (hs ep) x hp
      obtain ⟨w,hw⟩ := (hcode M _ ep).mp hnext
      change (parameterSide (stepSide pred)).Eval ![] e ∨
        (∃⁰ parameterMatrix (stepMatrix pred)).Eval ![] e
      right
      rw [Semiformula.eval_ex]
      refine ⟨w, (modelParameterMatrixAll (stepMatrix pred) w e).mpr ?_⟩
      apply (modelStepMatrix pred w v).mpr
      have hsingle : (![e 0] : Fin 1 → M) = (fun _ => e 0) := by
        funext i
        exact Fin.cases rfl (fun j => Fin.elim0 j) i
      simpa [v,x,y,ep,hsingle,Nat.add_assoc] using hw
    · change (parameterSide (stepSide pred)).Eval ![] e ∨
        (∃⁰ parameterMatrix (stepMatrix pred)).Eval ![] e
      left
      apply (modelParameterSideAll (stepSide pred) e).mpr
      exact (modelStepSide pred v).mpr hxy
  have hp := PRA_proves_rule_of_contextual_step pred hpbase hpstep
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hh := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hp
  simp only [models_iff, Semiformula.eval_univCl] at hh ⊢
  intro e
  have hforall := hh e
  simp only [Semiformula.eval_all] at hforall ⊢
  intro x
  apply (hcode M x e).mpr
  exact (modelExistentialBody pred x e).mp (hforall x)
end DiophantineConsistency.PRAPositiveAdmissible
