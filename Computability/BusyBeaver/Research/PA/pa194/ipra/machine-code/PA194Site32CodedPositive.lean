import PA194Site32ClockCodeFinal
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site32CodedPositive
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

theorem positivePath (k m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    F PA194Stepper.stepper ![F PA194Site32PositiveClockCode.clockCode (Fin.cons k args),
        PA194SourceSite31Physical.physicalFrame 32 ((k+1)+1) args] =
      PA194SourceSite31Physical.physicalFrame 33 (((k+1)+1)+1) (Function.update args 6 m) := by
  rw [PA194Site32PositiveClockCode.modelClock]
  exact PA194Site32PositivePathExact.positivePath k m args hm
#print axioms positivePath
end models
end PA194Site32CodedPositive
