import PA194AX11HCompare
import PA194AX11HCopyFirst
import PA194AX11HCopySecond
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194AX11HCompareExit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ClockInvariantDefinable
open PA194ModelMPDrain PA194AX11HCompareRows PA194AX11HCandidateDrain
open PA194ModelMPCompare (values)
open PA194AX11HCompare (Reaches append oneStep)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The successful branch adds D into T while restoring D and clearing X. -/
theorem copySuccess (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) :
    PA194AX11HCompare.Reaches (sourceState 3652 a tail)
      (sourceState 3659 (Function.update a 1 (a 1+a 4)) tail) :=
  PA194PausedReach.append (M := M) PA194AX11HSource.step
    (PA194AX11HCopyFirst.copyFirst (M := M) a tail hX)
    (PA194AX11HCopySecond.copySecond (M := M) a tail hX)


#print axioms copySuccess
end models
end PA194AX11HCompareExit
