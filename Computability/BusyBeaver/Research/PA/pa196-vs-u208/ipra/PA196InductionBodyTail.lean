import PA196InductionImpGrowth
import PA196InductionBodyAll

/-! An unconditional witness bound for the exact final tail of Foundation's
induction-body graph, composed with the two quantifier-code constructions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PA196InductionBodyTail
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAWitnessCalculus
open DiophantineConsistency.PRAWitnessTransfer DiophantineConsistency.PRAWitnessBoundTerms
open DiophantineConsistency.PRAWitnessBoundTerms.BoundTerm
open DiophantineConsistency.PRAWitnessCodeGrowth
open PA196InductionImpGrowth PA196InductionBodyAll
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- Bound the final implication witness of the actual body graph. -/
theorem wb_actualSecondTail : WB M actualSecondTail := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_impGraph (M := M)
  simp only [actualSecondTail, indBodyValGraph, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_bt _ (by simp) (tauT (poly ‘#0 + #1 + 8’) (poly ‘2 * (#0 + #1) + 10’))
    (fun V _ _ e u h => by
      have h' := h; simp at h'
      rw [h'.1]
      simpa [vval_tauT, vval, numeral_eq_natCast] using
        (imp_all (le_add_self (a := e 1) (b := e 0)) (le_self_add (a := e 0) (b := e 1)))) (by wb_auto)

/-- The two quantifier-code witnesses and the final implication witness are
all bounded, with no additional tail assumptions. -/
theorem wb_actualFirstExists : WB M actualFirstExists :=
  wb_both_actualExists wb_actualSecondTail

#print axioms wb_actualSecondTail
#print axioms wb_actualFirstExists
end PA196InductionBodyTail
