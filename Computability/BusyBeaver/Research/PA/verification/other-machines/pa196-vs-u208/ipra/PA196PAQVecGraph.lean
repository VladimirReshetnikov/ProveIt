import PA196PATermOperations

/-! Witness bounds for the actual arithmetic quantifier parameter-vector
graph. The intermediate shifted vector is bounded by the output's pair code. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PAQVecGraph
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
open PRAWitnessTransfer PRAWitnessVectors

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_qVecGraph : WB M (qVecGraph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_lenDef (M := M); have := PA196PATermOperations.wb_termBShiftVecGraph (M := M)
  have := wb_qqBvarDef (M := M); have := wb_adjoinDef (M := M)
  simp only [qVecGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) ?_
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#1’ (fun V _ _ e x h => ⟨x, ?_, h⟩) ?_
  · have h' := h
    simp at h'
    change x ≤ e 1
    rw [h'.2, adjoin_def]
    exact le_trans (le_pair_right _ _) le_self_add
  · wb_auto
    exact wb_exs_poly _ (by simp) ‘1’
      (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1, qqBvar, pair], h⟩) (by wb_auto)

#print axioms wb_qVecGraph
end PA196PAQVecGraph
