import PA196PASubstitutionTowerGraph
import PA194PAeqSubstStageUniform
import PA194PAeqSubstCore
import PA194PAeqFormulaRecWitness
import DiophantineConsistency.PRAWitnessFixpointGraph

/-! Witness extraction using the proved arithmetic stage bound. The two
candidate-PRA tower obligations and both core witness bounds remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace PA194PAeqSubstWitnessConditional
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PRAWitnessTransfer PRAWitnessFixpointGraph PA196PASubstitutionTowerGraph
  PA194PAeqSubstStageUniform PA196PAQVecTowerAlgebra

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

noncomputable def phi : Fixpoint.Blueprint 0 := (Substs.blueprint PA194PAeq.language).blueprint PA194PAeq.language

theorem wb_fixpoint_conditional
    (hσ : WB M phi.core.sigma.val) (hπ : WB M (∼phi.core.pi.val))
    (hdom : PRA ⊢ dominates towerGraph.val towerTerm)
    (hmono : Mono M (fun e : Fin 1 → M => towerTerm.val e Empty.elim)) :
    WB M phi.fixpointDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hl := PRAHistoryTruncation.wb_limSeqDef phi hσ hπ
  have hbit := PRAWitnessArithmetic.wb_bitDef (M := M)
  have hs : Hierarchy 𝚺 1 (stageFormula phi) := by
    simp [stageFormula, phi.limSeqDef.sigma_prop]
  have hWBs : WB M (stageFormula phi) := by
    simp only [stageFormula]
    refine wb_exs (fun e => PRAHistoryTruncation.histBound (e 0))
      (fun e e' h => PRAHistoryTruncation.histBound_mono (h 0)) ?_ (by wb_auto)
    rintro e ⟨L,hL⟩
    have hlim : phi.limSeqDef.val.Evalb (L :> e 0 :> fun i => e i.succ.succ) := by
      have h := hL
      simp [Semiformula.Operator.val, Matrix.comp_vecCons''] at h
      have he : (L :> e 0 :> fun i => e i.succ.succ) = ![L,e 0] := by
        funext i
        exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
      rw [he]
      exact h.1
    exact ⟨L, le_of_lt (show L < PRAHistoryTruncation.histBound (e 0) from
      PRAHistoryTruncation.limSeq_value_lt phi _ hlim), hL⟩
  rw [fixpointDef_eq]
  refine wb_exs_bound (stageFormula phi) hs towerGraph.val towerTerm hdom hmono ?_ hWBs
  intro V _ _ e s h
  obtain ⟨L,hL,hx⟩ : ∃ L, phi.limSeqDef.val.Evalb (L :> s :> fun i => e i.succ) ∧
      bitDef.val.Evalb ![e 0,L] := by
    simpa [stageFormula, Semiformula.Operator.val, operator_mem_def, Matrix.comp_vecCons'',
      PRAHistoryTruncation.val_comp_bvar] using h
  have hL' : L = (arithmeticFix (V := V)).limSeq ![] s := by
    simpa [phi, Matrix.empty_eq] using ((arithmeticFix (V := V)).eval_limSeqDef
      (L :> s :> fun i => e i.succ)).mp hL
  have hxL : e 0 ∈ L := by simpa [Semiformula.Operator.val, operator_mem_def] using hx
  have hst := subst_fixpoint_stage (hL' ▸ hxL)
  let t : V := iter (e 0 + 2) (4 * e 0 + 1)
  refine ⟨t, ?_, t, le_rfl, ?_⟩
  · have he : (t :> e) = ![t,e 0] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    rw [he]
    exact (towerGraph_eval (V := V) t (e 0)).mpr rfl
  · have hlt := ((arithmeticFix (V := V)).eval_limSeqDef
      (arithmeticStage t :> t :> fun i => e i.succ)).mpr (by simp [arithmeticStage, Matrix.empty_eq])
    have hlt' : phi.limSeqDef.val.Evalb ![arithmeticStage t,t] := by
      simpa [phi, Matrix.empty_eq] using hlt
    have hmem : e 0 ∈ arithmeticStage t := by simpa [t] using hst
    simpa [stageFormula, phi, Semiformula.Operator.val, operator_mem_def, Matrix.comp_vecCons'',
      PRAHistoryTruncation.val_comp_bvar] using ⟨arithmeticStage t, hlt', hmem⟩

#print axioms wb_fixpoint_conditional
end PA194PAeqSubstWitnessConditional
