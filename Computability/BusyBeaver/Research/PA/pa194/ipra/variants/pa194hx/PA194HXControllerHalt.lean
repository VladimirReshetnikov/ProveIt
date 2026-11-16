import PA194HXControllerAdvance
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194HXControllerHalt
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194CompressedSourceFrame PA194HXSourceArgs
open PA194CompressedBoxOracle PA194CompressedBoxFiles PA194CompressedIncrementOracle
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime

theorem haltControl : PA194HXRowData.denseControl 254 = 194 := by decide +kernel
/-- The exact native HX table takes the source halt site to halt. -/
theorem haltCheck10 : PA194HXContracts.cachedHalt 10 512 = true := by decide +kernel

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

theorem encodeControl (label : Nat → Nat) (gap : M) (box : BoxSt → M) (s : SConf) :
    π₁ (encode label gap box s) = (label s.1 : M) := by
  rcases s with ⟨q,onLeft,l,r⟩
  cases onLeft <;> simp [encode,scanFrame]

theorem halt_sound (gap : M) {box : BoxSt → M}
    (hb : BoxAgreement PA194HXDispatch.table PA194HXRowData.denseControl none box) (i fuel : Nat)
    (cert : PA194HXContracts.cachedHalt i fuel = true) :
    ∃ final, Reach1 PA194HXDispatch.table (PA194HXPhysicalConditional.root gap box i) final ∧
      π₁ final = (194 : M) := by
  let start := PA194RuntimeContracts.rootFrame (PA194SourceProgram.path i)
  change (exec PA194HXContracts.cachedMachine none (fun s => s.1 == 254) fuel start false).isSome = true at cert
  cases observed : exec PA194HXContracts.cachedMachine none (fun s => s.1 == 254) fuel start false with
  | none => simp [observed] at cert
  | some last =>
    obtain ⟨finished,_,positive⟩ :=
      checkedRun PA194HXRowAgreement.rowAgreement gap hb (fun s => s.1 == 254) fuel start last false observed
    refine ⟨encode PA194HXRowData.denseControl gap box last, positive rfl, ?_⟩
    rw [encodeControl, beq_iff_eq.mp finished, haltControl]
    rfl

/-- The modeled HX physical machine reaches its halt state from a site-10
    source root in positive model time, for arbitrary model-valued registers. -/
theorem site10Halts (s gap count spare : M) (hpc : F pc ![s] = modelNumeral M 10) :
    ∃ final, Reach1 PA194HXDispatch.table
      (F PA194HXSourceRoot.sourceRootCode ![s,gap,count,spare]) final ∧ π₁ final = (194 : M) := by
  let a := tapeArgs s count spare
  let inc := incremented a count
  let box := boxValue a inc
  have hb : BoxAgreement PA194HXDispatch.table PA194HXRowData.denseControl none box :=
    PA194HXBoxAgreement.concreteBoxAgreement a count none (readTail s count spare) trivial
  have hin : box (.plain .none) = F PA194HXAllocation.sourceFileCode (args s count spare) :=
    (frameFile s count spare).symm
  have he : PA194HXPhysicalConditional.root gap box 10 =
      F PA194HXSourceRoot.sourceRootCode ![s,gap,count,spare] := by
    rw [PA194HXSourceRoot.sourceRootCodeCorrect s gap count spare ⟨10,by decide⟩ hpc]
    simpa only [Nat.add_zero] using PA194HXRootEncoding.rootEncoding gap box 10 0 .none (args s count spare) hin
  simpa only [he] using halt_sound gap hb 10 512 haltCheck10

#print axioms haltCheck10
#print axioms halt_sound
#print axioms site10Halts
end models
end PA194HXControllerHalt
