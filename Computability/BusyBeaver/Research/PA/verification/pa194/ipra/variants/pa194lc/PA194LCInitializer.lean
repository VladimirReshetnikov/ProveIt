import PA194LCRoot
import PA194LCModelStartup
import PA194CompressedStartup
import PA194ModelDenseStartup

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194LCInitializer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PackedRootModel
open PA194LCRoot PA194CompressedStartup PA194HalfDiv PA194FiniteControls PA194UnaryRuns PA194ZeroRuns

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem seedPath : PA194LCData.path 25 = PA194SourceProgram.path 25 := by decide +kernel
private theorem seedGap : 48 - (PA194LCData.path 25).length = 42 := by decide +kernel

theorem startup_root :
    ConPA.Machine.run (V := M) PA194LCData.table (58154 : M) =
      F sourceRootCode ![initialSource,0,modelNumeral M 25,initialSpare] := by
  have hp := PA194ModelDenseStartup.modelDenseStartup (M := M)
  have hr := PA194CompressedStartup.blankToRoot (M := M)
  rw [show modelNumeral M 0 = (0 : M) from rfl] at hp
  rw [sourceRoot_eval _ _ _ _ ⟨25,by decide⟩ initialPC, seedArguments, root_eval]
  simp only [Nat.add_zero, zero_add]
  change _ = ⟪(24 : M),(1 : M),PA194Path27Header.modelWord (PA194LCData.path 25)
    (F zeros ![modelNumeral M (48 - (PA194LCData.path 25).length),
      F pushOne (fun _ => F PA194RegisterPermutation.sourceFileCode startArgs)])⟫
  rw [seedGap, seedPath, PA194LCModelStartup.modeledStartup]
  have h : PA194SourceSite31Physical.physicalFrame 25 (modelNumeral M 42)
      (startArgs (M := M)) =
    ⟪(24 : M),(1 : M),(PA194Bounded.bits PA194StartupData.seedFrame.r : M)⟫ := by
    rw [← hr, hp]
    simp only [modelNumeralCast, modelPairCode, Nat.cast_ofNat, Nat.cast_one]
  have hbits : PA194Bounded.bits PA194StartupData.seedFrame.r =
      152919395647067130113387679226998336721518593 := by decide +kernel
  rw [hbits] at h
  simp only [Nat.cast_ofNat] at h
  rw [← h]
  unfold PA194SourceSite31Physical.physicalFrame
  simp only [modelPairCode, modelNumeralCast, Nat.cast_ofNat, modelPushOne]
  have he (x : M) : x+x+1 = 1+(x+x) := by ac_rfl
  rw [he]

#print axioms startup_root
end models
end PA194LCInitializer
