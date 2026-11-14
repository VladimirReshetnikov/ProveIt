import PA194PAeqFormulaWitness
import DiophantineConsistency.PRAWitnessFormulaRec

/-! PAeq-language specialization of the ranked formula-recursion witness
bounds. The recursion's clause and shape certificates remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PAeqFormulaRecWitness
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.StrictSigmaOneInduction DiophantineConsistency.PRAWitnessCalculus DiophantineConsistency.PRAWitnessArithmetic
open DiophantineConsistency.PRAWitnessFormulaRec PA194PAeqFormulaWitness
open DiophantineConsistency.PRAWitnessVectors DiophantineConsistency.PRAWitnessFixpointGraph
open DiophantineConsistency.PRAModelIOpenPairing DiophantineConsistency.PRAWitnessTransfer

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable {β : UformulaRec1.Blueprint}

theorem wb_core_sigma (hβ : ClauseBounds β M) : WB M (β.blueprint PA194PAeq.language).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hβ.rel; have := hβ.nrel; have := hβ.verum; have := hβ.falsum; have := hβ.and
  have := hβ.or; have := hβ.all; have := hβ.exs; have := hβ.allChanges; have := hβ.exsChanges
  have := wb_formula_sigma_complete (M := M); have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
  have := wb_qqVerumDef (M := M); have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M)
  have := wb_qqOrDef (M := M); have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_pair₃Def (M := M); have := wb_memRel₃ (M := M)
  have : WB M memRel₃Opr.sentence := wb_memRel₃ (M := M)
  simp only [UformulaRec1.Blueprint.blueprint, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  all_goals
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#6’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa using le_of_lt (lt_of_le_of_lt (le_pair_left u _) (lt_of_mem h'.2)), h⟩) (by wb_auto)

theorem wb_core_neg_pi (hβ : ClauseBounds β M) : WB M (∼(β.blueprint PA194PAeq.language).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hβ.rel_pi; have := hβ.nrel_pi; have := hβ.verum_pi; have := hβ.falsum_pi; have := hβ.and_pi
  have := hβ.or_pi; have := hβ.all_pi; have := hβ.exs_pi; have := hβ.allChanges; have := hβ.exsChanges
  have := wb_formula_neg_pi_complete (M := M); have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
  have := wb_qqVerumDef (M := M); have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M)
  have := wb_qqOrDef (M := M); have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_pair₃Def (M := M); have := wb_memRel₃ (M := M); have := wb_neg_memRel₃ (M := M)
  have : WB M memRel₃Opr.sentence := wb_memRel₃ (M := M)
  have : WB M (∼memRel₃Opr.sentence) := wb_neg_memRel₃ (M := M)
  have := wb_neg_pair₃Def (M := M); have := wb_neg_qqRelDef (M := M); have := wb_neg_qqNRelDef (M := M)
  have := wb_neg_qqVerumDef (M := M); have := wb_neg_qqFalsumDef (M := M)
  have := wb_neg_qqAndDef (M := M); have := wb_neg_qqOrDef (M := M); have := wb_neg_qqAllDef (M := M)
  have := wb_neg_qqExsDef (M := M)
  simp only [UformulaRec1.Blueprint.blueprint, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  all_goals
    refine PRAWitnessTransfer.wb_exs_bound _ (by simp)
      (PRAWitnessExpBounds.expGraph2 ‘#4 + 4’ ‘2 * #4 + 4’)
      (PRAWitnessExpBounds.expBound2 ‘#4 + 4’ ‘2 * #4 + 4’)
      (PRAWitnessExpBounds.dominates_expBound2 _ _) (PRAWitnessExpBounds.mono_expBound2 _ _)
      (fun V _ _ e u h => ?_) (by wb_auto)
    have h' := h; simp at h'
    refine ⟨Exp.exp ((e 4 + 4) * Exp.exp (2 * e 4 + 4)), ?_, u, ?_, h⟩
    · rw [PRAWitnessExpBounds.eval_expGraph2]
      exact ⟨_, by simpa using exponential_exp (2 * e 4 + 4), by simpa using exponential_exp _⟩
    · first
      | exact hβ.allChanges_le V u (e 4) h'.1
      | exact hβ.exsChanges_le V u (e 4) h'.1


theorem wb_graph_of_fixpoint (hfix : WB M (β.blueprint PA194PAeq.language).fixpointDef.val) :
    WB M (β.graph PA194PAeq.language).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hfix; have := wb_pair₃Def (M := M)
  simp only [UformulaRec1.Blueprint.graph, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_term
    ‘(#0 + (#1 + #2 + 1) * (#1 + #2 + 1) + 1) * (#0 + (#1 + #2 + 1) * (#1 + #2 + 1) + 1)’
    (fun e u h => ?_) (by wb_auto)
  simp [pair₃Def] at h
  rw [h.1.2]
  simpa [triplePoly] using pair3_le_triplePoly (e 0) (e 1) (e 2)

theorem wb_result_of_fixpoint (hfix : WB M (β.blueprint PA194PAeq.language).fixpointDef.val) :
    WB M (β.result PA194PAeq.language).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_graph_of_fixpoint hfix; have := wb_formula_sigma_complete (M := M)
  have := wb_formula_neg_pi_complete (M := M)
  simp only [UformulaRec1.Blueprint.result, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto


#print axioms wb_result_of_fixpoint
#print axioms wb_core_sigma
#print axioms wb_core_neg_pi
end PA194PAeqFormulaRecWitness
