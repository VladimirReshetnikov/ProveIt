import PA194Site35FirstPassGeneral
import PA194Site35SecondPrefix
import PA194Site34PositivePath
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site35SecondTo71
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

theorem to71 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let f := F sourceFileCode args
    let d := (1 : M)+(f+f)
    let v := (1 : M)+(d+d)
    let c := F addCode ![F addCode ![modelNumeral M 10,n+1],(1 : M)]
    let first := F addCode ![F addCode ![c,(k+1)+1],modelNumeral M 24]
    F PA194Stepper.stepper ![F addCode ![first,modelNumeral M 9],
      PA194SourceSite31Physical.physicalFrame 35 n args] =
      F pairCode ![modelNumeral M 71,F pairCode ![modelNumeral M 804,F ones ![k,v]]] := by
  dsimp only
  let f := F sourceFileCode args
  let d := (1 : M)+(f+f)
  let v := (1 : M)+(d+d)
  let w := F ones ![k+1,v]
  have hw : w = F ones ![k,v]+F ones ![k,v]+1 := by
    dsimp only [w]
    change F ones ![F addCode ![k,F oneCode Fin.elim0],v] = _
    rw [modelAddOne,modelOnesSucc]
  have h := PA194Site35FirstPassGeneral.firstPass k args
  dsimp only at h
  change _ = F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 35) w]] at h
  rw [PA194Site34PositivePath.path35,hw] at h
  have hp := PA194Site35SecondPrefix.prefixWord (F ones ![k,v])
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false,modelNumeralOne] at hp
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false] at h
  rw [PA194StepperCompose.modelStepperCompose,h,hp]
#print axioms to71
end models
end PA194Site35SecondTo71
