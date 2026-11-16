import PA196PAFormulaRecBound
import PA196PABvGrowth
import DiophantineConsistency.PRAWitnessFormulaFunctions

/-! The arithmetic bound-variable formula graph has a witness bound when the
arithmetic term-vector bound-variable graph does. The latter is an explicit
hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PABvGraphBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
open PRAWitnessExpBounds PRAWitnessTransfer PRAWitnessFormulaFunctions PA196PABvGrowth
open PRAWitnessRepeatVec PRAWitnessTermRec

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem bv_clauses (hv : WB M (termBVVecGraph ℒₒᵣ).val) : PRAWitnessFormulaRec.ClauseBounds (BV.blueprint ℒₒᵣ) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hv; have := PRAWitnessTermFunctions.wb_listMaxDef (M := M)
  have := PRAWitnessTermFunctions.wb_maxDef (M := M)
  have := wb_subDef (M := M)
  have ⟨h_rel, h_nrel⟩ :
      WB M (BV.blueprint ℒₒᵣ).rel.val ∧ WB M (BV.blueprint ℒₒᵣ).nrel.val := by
    constructor <;>
      simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma] <;>
      refine PRAWitnessTransfer.wb_exs_bound _ (by simp)
        (expGraph2 ‘#4 + 2’ ‘2 * #2’) (expBound2 ‘#4 + 2’ ‘2 * #2’)
        (dominates_expBound2 _ _) (mono_expBound2 _ _) (fun V _ _ e x h => ?_) (by wb_auto)
    all_goals
      have h' := h; simp at h'
      refine ⟨Exp.exp ((e 4 + 2) * Exp.exp (2 * e 2)), ?_, x, ?_, h⟩
      · rw [eval_expGraph2]
        exact ⟨Exp.exp (2 * e 2), by simpa using exponential_exp (2 * e 2),
          by simpa using exponential_exp ((e 4 + 2) * Exp.exp (2 * e 2))⟩
      · rw [h'.1]; exact le_trans (termBVVec_le _ _) (le_of_lt (repeatVec_lt _ _))
  have ⟨h_verum, h_falsum, h_and, h_or, h_all, h_exs, h_allChanges, h_exsChanges⟩ :
      WB M (BV.blueprint ℒₒᵣ).verum.val ∧ WB M (BV.blueprint ℒₒᵣ).falsum.val ∧
      WB M (BV.blueprint ℒₒᵣ).and.val ∧ WB M (BV.blueprint ℒₒᵣ).or.val ∧
      WB M (BV.blueprint ℒₒᵣ).all.val ∧ WB M (BV.blueprint ℒₒᵣ).exs.val ∧
      WB M (BV.blueprint ℒₒᵣ).allChanges.val ∧ WB M (BV.blueprint ℒₒᵣ).exsChanges.val := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [BV.blueprint, HierarchySymbol.Semiformula.val_mkSigma] <;> wb_auto
  refine ⟨h_rel, h_nrel, h_verum, h_falsum, h_and, h_or, h_all, h_exs, h_allChanges, h_exsChanges,
    wb_neg_graphDelta_pi _ h_rel ‘#3’ ?_, wb_neg_graphDelta_pi _ h_nrel ‘#3’ ?_,
    wb_neg_graphDelta_pi _ h_verum ‘0’ ?_, wb_neg_graphDelta_pi _ h_falsum ‘0’ ?_,
    wb_neg_graphDelta_pi _ h_and ‘#3 + #4’ ?_, wb_neg_graphDelta_pi _ h_or ‘#3 + #4’ ?_,
    wb_neg_graphDelta_pi _ h_all ‘#2’ ?_, wb_neg_graphDelta_pi _ h_exs ‘#2’ ?_, ?_, ?_⟩
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simpa using PA196PABvGrowth.listMax_termBVVec_le (e 1) (e 3)
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simpa using PA196PABvGrowth.listMax_termBVVec_le (e 1) (e 3)
  · intro V _ _ e y h; simp [BV.blueprint] at h; simp [h]
  · intro V _ _ e y h; simp [BV.blueprint] at h; simp [h]
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simp
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simp
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simp
  · intro V _ _ e y h; simp [BV.blueprint] at h; rw [h]; simp
  · intro V _ _ a b h; simp [BV.blueprint] at h; simp [h]
  · intro V _ _ a b h; simp [BV.blueprint] at h; simp [h]

noncomputable abbrev bvConstructions : PRAWitnessFormulaRec.Constructions (BV.blueprint ℒₒᵣ) :=
  fun _ _ _ => BV.construction ℒₒᵣ

theorem bv_shape (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    PRAWitnessFormulaRec.RecShape (bvConstructions V) where
  all_le _ := by simp [BV.construction]
  exs_le _ := by simp [BV.construction]
  and_le _ _ _ y₁ y₂ := by
    simp only [BV.construction]
    exact ⟨le_trans (le_max_left y₁ y₂) le_self_add, le_trans (le_max_right y₁ y₂) le_self_add⟩
  or_le _ _ _ y₁ y₂ := by
    simp only [BV.construction]
    exact ⟨le_trans (le_max_left y₁ y₂) le_self_add, le_trans (le_max_right y₁ y₂) le_self_add⟩
  all_y _ _ y₁ := by simp only [BV.construction]; exact le_tsub_add
  exs_y _ _ y₁ := by simp only [BV.construction]; exact le_tsub_add

theorem wb_bvGraph (hv : WB M (termBVVecGraph ℒₒᵣ).val) : WB M (bvGraph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [bvGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (PA196PAFormulaRecBound.wb_result bvConstructions bv_shape (bv_clauses hv))

#print axioms wb_bvGraph
end PA196PABvGraphBound
