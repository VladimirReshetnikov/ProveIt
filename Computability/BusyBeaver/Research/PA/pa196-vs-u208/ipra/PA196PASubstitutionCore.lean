import PA196PASubstitutionNegative
import PA196PAQVecGrowth
import PA196PAFormulaRecBound

/-! The actual arithmetic substitution recursion core has a positive witness
bound. Its negative-pi bound follows from the two remaining relation-clause
bounds; arithmetic qVec growth is handled unconditionally. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PASubstitutionCore
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
open PRAWitnessFormulaRec PA196PAFormulaComplete PRAWitnessVectors
open PRAModelIOpenPairing PRAWitnessTransfer

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_core_sigma : WB M ((Substs.blueprint ℒₒᵣ).blueprint ℒₒᵣ).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := PA196PASubstitutionClauses.positive_clauses (M := M)
  have := h1; have := h2; have := h3; have := h4; have := h5
  have := h6; have := h7; have := h8; have := h9; have := h10
  have := wb_isUFormula_sigma (M := M); have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
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

theorem wb_core_neg_pi
    (hrel : WB M (∼(Substs.blueprint ℒₒᵣ).rel.graphDelta.pi.val))
    (hnrel : WB M (∼(Substs.blueprint ℒₒᵣ).nrel.graphDelta.pi.val)) :
    WB M (∼((Substs.blueprint ℒₒᵣ).blueprint ℒₒᵣ).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨_,_,_,_,_,_,_,_,h9,h10⟩ := PA196PASubstitutionClauses.positive_clauses (M := M)
  obtain ⟨h3,h4,h5,h6,h7,h8⟩ := PA196PASubstitutionNegative.negative_constructor_clauses (M := M)
  have := hrel; have := hnrel; have := h3; have := h4; have := h5
  have := h6; have := h7; have := h8; have := h9; have := h10
  have := wb_isUFormula_neg_pi (M := M); have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
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
      (PRAWitnessExpBounds.expGraph2 ‘#4 + 8 + 4’ ‘22 * #4 + 22’)
      (PRAWitnessExpBounds.expBound2 ‘#4 + 8 + 4’ ‘22 * #4 + 22’)
      (PRAWitnessExpBounds.dominates_expBound2 _ _) (PRAWitnessExpBounds.mono_expBound2 _ _)
      (fun V _ _ e u h => ?_) (by wb_auto)
    have h' := h; simp at h'
    refine ⟨Exp.exp ((e 4 + 8 + 4) * Exp.exp (22 * e 4 + 22)), ?_, u, ?_, h⟩
    · rw [PRAWitnessExpBounds.eval_expGraph2]
      exact ⟨_, by simpa [numeral_eq_natCast] using exponential_exp (22 * e 4 + 22),
        by simpa [numeral_eq_natCast] using exponential_exp _⟩
    · simp only [Substs.blueprint, HierarchySymbol.Semiformula.val_mkSigma] at h'
      simp at h'
      rw [h'.1]
      simpa [PRAWitnessCodeGrowth.tau] using PA196PAQVecGrowth.qVec_le (e 4)

#print axioms wb_core_sigma
#print axioms wb_core_neg_pi
end PA196PASubstitutionCore
