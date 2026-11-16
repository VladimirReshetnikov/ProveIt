import PA194P5Allocation
import PA194P5ModelStartup
import PA194RegisterRoot
import PA194CompressedStartup
import PA194ModelDenseStartup

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194P5Seed
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194CompressedStartup PA194RegisterLayout PA194RegisterRoot PA194P5Allocation
open PA194CompressedBoxFiles

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

private theorem numeralCast (n : Nat) : modelNumeral M n = (n : M) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [modelNumeralSucc,ih,Nat.cast_succ]

theorem seedRight : PA194Bounded.bits PA194StartupData.seedFrame.r =
    152919395647067130113387679226998336721518593 := by decide +kernel

/-- The only nonzero logical register is N, in physical position 6 in both layouts. -/
theorem seedFile :
    file (tapeArgs allocation (initialSource : M) (modelNumeral M 25) initialSpare) =
      F PA194RegisterPermutation.sourceFileCode startArgs := by
  rw [tapeArgs, seedArguments, PA194RegisterPermutation.modelSourceFile]
  apply congrArg (F (PA194RegisterFile.fileCode 10))
  funext i
  fin_cases i <;> rfl

theorem startup_root :
    ConPA.Machine.run PA194P5Data.table (56158 : M) =
      F (sourceRootCode allocation) ![initialSource, 0, modelNumeral M 25, initialSpare] := by
  rw [sourceRootCodeCorrect allocation _ _ _ _ ⟨25, by decide⟩ initialPC, zero_add, seedFile]
  have gap : 48 - (PA194SourceProgram.path 25).length = 42 := by
    rw [PA194Path27Frame.path25]
    rfl
  rw [gap]
  change _ = PA194SourceSite31Physical.physicalFrame 25 (modelNumeral M 42) startArgs
  rw [← blankToRoot, PA194P5ModelStartup.modeledStartup]
  have hp := PA194ModelDenseStartup.modelDenseStartup (M := M)
  rw [seedRight, show modelNumeral M 0 = (0 : M) from rfl] at hp
  rw [hp]
  simp only [numeralCast, modelPairCode, Nat.cast_ofNat, Nat.cast_one]

#print axioms seedFile
#print axioms startup_root
end models
end PA194P5Seed
