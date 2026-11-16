import PA194GuardedShortcuts
import PA194ControllerNative

set_option autoImplicit false

namespace PA194FastController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open ConPA.MachineEndpoint PA194GuardedShortcuts TableDispatch

/-- The two literal shortcuts preserve the calibrated source comparison. -/
theorem sameSource (C : Certificate)
    (prior : PA194ControllerNative.SameSourceHalt (originalTable C) 194) :
    PA194ControllerNative.SameSourceHalt (acceleratedTable C) 194 := by
  intro M _ _ _ _
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  dsimp only
  intro _
  exact (sameHalt (V := M) C).symm.trans (prior M)

theorem consistency_iff (C : Certificate)
    (prior : PA194ControllerNative.SameSourceHalt (originalTable C) 194) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence (acceleratedTable C) 194 :=
  PA194ControllerNative.consistency_iff (acceleratedTable C) 194 (sameSource C prior)

#print axioms consistency_iff
end PA194FastController
