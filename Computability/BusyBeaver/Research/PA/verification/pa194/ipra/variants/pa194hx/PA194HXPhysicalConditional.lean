import PA194HXRowAgreement
import PA194HXContractSound
import ConPAMachineCompressedNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194HXPhysicalConditional
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.Runtime
open ConPA.Machine ConPA.Machine.Compressed
open PA194HXRowData PA194HXRowAgreement PA194SourceProgram

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def root (gap : V) (box : BoxSt → V) (i : Nat) (extra : Nat := 0)
    (effect : Eff := .none) : V :=
  encode denseControl gap box (PA194RuntimeContracts.rootFrame (path i) extra effect)

/-- Every successfully checked symbolic HX instruction segment gives a real
    positive-duration HX table segment, conditional on the exact HX box oracle. -/
theorem cached_contract_sound (gap : V) {br : Branch} {box : BoxSt → V}
    (hb : BoxAgreement PA194HXDispatch.table denseControl br box)
    (i j extra fuel : Nat) (effect : Eff)
    (cert : PA194HXContracts.cachedContract br i j extra fuel effect = true) :
    Reach1 PA194HXDispatch.table (root gap box i) (root gap box j extra effect) := by
  change (exec PA194HXContracts.cachedMachine br
    (fun s => sMatches s (PA194RuntimeContracts.rootFrame (path j) extra effect))
    fuel (PA194RuntimeContracts.rootFrame (path i)) false).isSome = true at cert
  exact checkedMatch PA194HXRowAgreement.rowAgreement gap hb fuel _ _ cert

theorem contract_sound (gap : V) {br : Branch} {box : BoxSt → V}
    (hb : BoxAgreement PA194HXDispatch.table denseControl br box)
    (i j extra fuel : Nat) (effect : Eff)
    (cert : PA194HXContractSound.contract br i j extra fuel effect = true) :
    Reach1 PA194HXDispatch.table (root gap box i) (root gap box j extra effect) := by
  apply cached_contract_sound gap hb i j extra fuel effect
  rw [PA194HXContractSound.cachedContractCorrect]
  exact cert

#print axioms cached_contract_sound
#print axioms contract_sound
end models
end PA194HXPhysicalConditional
