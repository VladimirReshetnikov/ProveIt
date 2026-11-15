import PA194Site32ZeroClockCode
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site32CodedZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194StartupSentence
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem zeroPath (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    F PA194Stepper.stepper ![F PA194Site32ZeroClockCode.clockCode (Fin.cons k args),
        PA194SourceSite31Physical.physicalFrame 32 ((k+1)+1) args] =
      PA194SourceSite31Physical.physicalFrame 34 (((k+1)+1)+1) args := by
  rw [PA194Site32ZeroClockCode.modelClock]
  exact PA194Site32ZeroPathExact.zeroPath k args hz
#print axioms zeroPath
end models
end PA194Site32CodedZero
