import PA194Site34FirstPassGeneral
import PA194Site34SecondPrefix
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34To93
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to93 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let f := F sourceFileCode args
    let d := (1 : M)+(f+f)
    let v := (1 : M)+(d+d)
    let z := F ones ![k,v]
    let c := F addCode ![F addCode ![modelNumeral M 13,n+1],(1 : M)]
    let first := F addCode ![F addCode ![c,(k+1)+1],modelNumeral M 23]
    F PA194Stepper.stepper ![F addCode ![first,modelNumeral M 8],
      PA194SourceSite31Physical.physicalFrame 34 n args] =
      F pairCode ![modelNumeral M 93,F pairCode ![modelNumeral M 400,z]] := by
  dsimp only
  let f := F sourceFileCode args
  let d := (1 : M)+(f+f)
  let v := (1 : M)+(d+d)
  let z := F ones ![k,v]
  have hw : F ones ![k+1,v] = z+z+1 := by
    dsimp only [z]
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hin : modelWord (PA194SourceProgram.path 34) (F ones ![k+1,v]) =
      modelWord [true,false,false,true,false,false,false,true] z := by
    rw [PA194Path34Header.path34,hw]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  have h := PA194Site34FirstPassGeneral.firstPass k args
  dsimp only at h
  rw [hin] at h
  have hp := PA194Site34SecondPrefix.prefixWord z
  simp only [modelNumeralOne] at hp
  rw [PA194StepperCompose.modelStepperCompose,h,hp]
  rfl
#print axioms to93
end models
end PA194Site34To93
