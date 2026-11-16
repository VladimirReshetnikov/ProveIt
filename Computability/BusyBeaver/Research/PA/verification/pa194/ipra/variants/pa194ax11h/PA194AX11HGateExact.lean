import PA194AX11HGateCopy
import PA194AX11HGateCompare
import PA194ModelMPTransfer
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194AX11HGateExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194ModelMPDrain
open PA194AX11HCandidateDrain PA194AX11HGateBinding PA194ModelAXGate PA194ModelMPTransfer

theorem rows3523 : PA194AX11HGateCompare.CompareRows 3523 := by
  refine ⟨by decide,
    by simpa using (gate_row ⟨4,by decide⟩).trans PA194AXGateRows.s3523,
    by simpa using (gate_row ⟨5,by decide⟩).trans PA194AXGateRows.s3524,
    by simpa using (gate_row ⟨6,by decide⟩).trans PA194AXGateRows.s3525,
    by simpa using (gate_row ⟨7,by decide⟩).trans PA194AXGateRows.s3526,
    by simpa using (gate_row ⟨8,by decide⟩).trans PA194AXGateRows.s3527,
    by simpa using (gate_row ⟨9,by decide⟩).trans PA194AXGateRows.s3528,
    by simpa using (gate_row ⟨10,by decide⟩).trans PA194AXGateRows.s3529,
    by simpa using (gate_row ⟨11,by decide⟩).trans PA194AXGateRows.s3530,
    by simpa using (gate_row ⟨12,by decide⟩).trans PA194AXGateRows.s3531,
    by simpa using (gate_row ⟨13,by decide⟩).trans PA194AXGateRows.s3532,
    by simpa using (gate_row ⟨14,by decide⟩).trans PA194AXGateRows.s3533,
    by simpa using (gate_row ⟨15,by decide⟩).trans PA194AXGateRows.s3534⟩
theorem rows3541 : PA194AX11HGateCompare.CompareRows 3541 := by
  refine ⟨by decide,
    by simpa using (gate_row ⟨22,by decide⟩).trans PA194AXGateRows.s3541,
    by simpa using (gate_row ⟨23,by decide⟩).trans PA194AXGateRows.s3542,
    by simpa using (gate_row ⟨24,by decide⟩).trans PA194AXGateRows.s3543,
    by simpa using (gate_row ⟨25,by decide⟩).trans PA194AXGateRows.s3544,
    by simpa using (gate_row ⟨26,by decide⟩).trans PA194AXGateRows.s3545,
    by simpa using (gate_row ⟨27,by decide⟩).trans PA194AXGateRows.s3546,
    by simpa using (gate_row ⟨28,by decide⟩).trans PA194AXGateRows.s3547,
    by simpa using (gate_row ⟨29,by decide⟩).trans PA194AXGateRows.s3548,
    by simpa using (gate_row ⟨30,by decide⟩).trans PA194AXGateRows.s3549,
    by simpa using (gate_row ⟨31,by decide⟩).trans PA194AXGateRows.s3550,
    by simpa using (gate_row ⟨32,by decide⟩).trans PA194AXGateRows.s3551,
    by simpa using (gate_row ⟨33,by decide⟩).trans PA194AXGateRows.s3552⟩

theorem row3535 : PA194AX11HSource.program[3535]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 7 (some 3538) (some 3536)) := by
  simpa using (gate_row ⟨16,by decide⟩).trans PA194AXGateRows.s3535
theorem row3536 : PA194AX11HSource.program[3536]'(by rw [PA194AX11HSource.program_length]; decide) = some (.inc 6 (some 3537)) := by
  simpa using (gate_row ⟨17,by decide⟩).trans PA194AXGateRows.s3536
theorem row3537 : PA194AX11HSource.program[3537]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3535)) := by
  simpa using (gate_row ⟨18,by decide⟩).trans PA194AXGateRows.s3537
theorem row3538 : PA194AX11HSource.program[3538]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 4 (some 3541) (some 3539)) := by
  simpa using (gate_row ⟨19,by decide⟩).trans PA194AXGateRows.s3538
theorem row3539 : PA194AX11HSource.program[3539]'(by rw [PA194AX11HSource.program_length]; decide) = some (.inc 5 (some 3540)) := by
  simpa using (gate_row ⟨20,by decide⟩).trans PA194AXGateRows.s3539
theorem row3540 : PA194AX11HSource.program[3540]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3538)) := by
  simpa using (gate_row ⟨21,by decide⟩).trans PA194AXGateRows.s3540

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

theorem transfer76 (a : Fin 11 → M) (tail : M) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 3535 a tail)
      (sourceState 3538 (transferArgs a 7 6) tail) := by
  have path : CandidateIncrements 3535 3536 [6] :=
    .inc _ _ _ _ (by decide) row3536 (.jump _ (by decide) row3537)
  have h := drain 3535 3536 3538 7 [6] (by decide) row3535 path (by decide) a tail
  rwa [transferArgs_eq a 7 6 (by decide)] at h

theorem transfer45 (a : Fin 11 → M) (tail : M) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 3538 a tail)
      (sourceState 3541 (transferArgs a 4 5) tail) := by
  have path : CandidateIncrements 3538 3539 [5] :=
    .inc _ _ _ _ (by decide) row3539 (.jump _ (by decide) row3540)
  have h := drain 3538 3539 3541 4 [5] (by decide) row3538 path (by decide) a tail
  rwa [transferArgs_eq a 4 5 (by decide)] at h

/-- The exact gate ends at revised source site 3553 before its inserted push. -/
theorem gate (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 3519 a tail)
      (sourceState 3553 (result a) tail) := by
  classical
  let b := copied a
  let c := PA194AX11HGateCompare.output b
  let d := transferArgs c 7 6
  let e := transferArgs d 4 5
  have hb := PA194AX11HGateCopy.copy a tail
  have hc := PA194AX11HGateCompare.compare 3523 rows3523 b tail
  have hd := transfer76 c tail
  have he := transfer45 d tail
  have hf := PA194AX11HGateCompare.compare 3541 rows3541 e tail
  have hout : PA194AX11HGateCompare.output e = result a := by
    funext i
    fin_cases i <;>
      by_cases hd : a 4 = a 3 <;> by_cases hh : a 5 = a 3 <;>
      simp [e,d,c,b,copied,PA194AX11HGateCompare.output,PA194ModelMPCompare.values,
        transferArgs,location,result,hx,hy,hd,hh]
  rw [hout] at hf
  exact PA194PausedReach.append _ (PA194PausedReach.append _ (PA194PausedReach.append _
    (PA194PausedReach.append _ hb hc) hd) he) hf
#print axioms gate
end models
end PA194AX11HGateExact
