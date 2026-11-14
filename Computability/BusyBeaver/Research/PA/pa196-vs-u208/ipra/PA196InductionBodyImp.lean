import PA196InductionBodyTail

/-! The middle implication witness in Foundation's exact induction-body graph
is bounded in every candidate-PRA model; its trailing graph is already bounded. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PA196InductionBodyImp
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAWitnessCalculus
open DiophantineConsistency.PRAWitnessTransfer DiophantineConsistency.PRAWitnessBoundTerms
open DiophantineConsistency.PRAWitnessBoundTerms.BoundTerm
open DiophantineConsistency.PRAWitnessCodeGrowth
open PA196InductionImpGrowth
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The exact scope of `∃ i1` in the original body graph. -/
noncomputable def actualImpExists : ArithmeticSemisentence 4 :=
  match indBodyValGraph.val with
  | .exs (.and _ (.exs (.and _ body))) => body
  | _ => ⊥

/-- The next conjunct is the previously bounded exact first-quantifier scope. -/
theorem actualImpExists_eq : actualImpExists =
    ∃⁰ (Rewriting.subst (impGraph ℒₒᵣ).val ![#0,#4,#1] ⋏ PA196InductionBodyAll.actualFirstExists) := by rfl

theorem wb_actualImpExists : WB M actualImpExists := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_impGraph (M := M)
  have := PA196InductionBodyTail.wb_actualFirstExists (M := M)
  rw [actualImpExists_eq]
  refine wb_exs_bt _ (by simp [PA196InductionBodyAll.actualFirstExists, indBodyValGraph])
    (tauT (poly ‘#0 + #3 + 8’) (poly ‘2 * (#0 + #3) + 10’))
    (fun V _ _ e u h => by
      have h' := h; simp at h'
      rw [h'.1]
      simpa [vval_tauT, vval, numeral_eq_natCast] using
        (imp_all (le_add_self (a := e 3) (b := e 0)) (le_self_add (a := e 0) (b := e 3)))) (by wb_auto)

#print axioms wb_actualImpExists
end PA196InductionBodyImp
