import PA194AX11HGateBinding
import PA194AX11HCandidateDrain
import PA194ModelAXGate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194AX11HGateCopy
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194ModelMPDrain
open PA194AX11HCandidateDrain PA194AX11HGateBinding PA194ModelAXGate

theorem row3519 : PA194AX11HSource.program[3519]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 3 (some 3523) (some 3520)) := by
  simpa using (gate_row ⟨0,by decide⟩).trans PA194AXGateRows.s3519
theorem row3520 : PA194AX11HSource.program[3520]'(by rw [PA194AX11HSource.program_length]; decide) = some (.inc 7 (some 3521)) := by
  simpa using (gate_row ⟨1,by decide⟩).trans PA194AXGateRows.s3520
theorem row3521 : PA194AX11HSource.program[3521]'(by rw [PA194AX11HSource.program_length]; decide) = some (.inc 6 (some 3522)) := by
  simpa using (gate_row ⟨2,by decide⟩).trans PA194AXGateRows.s3521
theorem row3522 : PA194AX11HSource.program[3522]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3519)) := by
  simpa using (gate_row ⟨3,by decide⟩).trans PA194AXGateRows.s3522
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem copy (a : Fin 11 → M) (tail : M) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 3519 a tail)
      (sourceState 3523 (copied a) tail) := by
  have path : CandidateIncrements 3519 3520 [7,6] :=
    .inc _ _ _ _ (by decide) row3520 <|
    .inc _ _ _ _ (by decide) row3521 <|
    .jump _ (by decide) row3522
  have h := drain 3519 3520 3523 3 [7,6] (by decide) row3519 path (by decide) a tail
  rwa [copyOut] at h
#print axioms copy
end models
end PA194AX11HGateCopy
