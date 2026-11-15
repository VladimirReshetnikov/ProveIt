import PA194Site34SecondPass
import PA194Site34ThirdPrefix
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34ThirdTo1
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def secondClock (k : M) (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  let back := (e 0+1)+(((k+1)+1)+1)
  F addCode ![F addCode ![F addCode ![PA194Site34SecondTo17.to14Clock k args,modelNumeral M 3],back],modelNumeral M 24]

theorem to1 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let tail := F (fileCode 8) (fun i => e i.succ.succ)
    let u := F ones ![e 1,tail]
    let c := (u+u)+(u+u)
    let w := F ones ![e 0,(1 : M)+c+c]
    let z := F ones ![k,(1 : M)+(w+w)+(w+w)]
    F PA194Stepper.stepper ![F addCode ![secondClock k args,modelNumeral M 13],
      PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 1,F pairCode ![modelNumeral M 800,z]] := by
  dsimp only
  let e := physicalArgs args
  let tail := F (fileCode 8) (fun i => e i.succ.succ)
  let u := F ones ![e 1,tail]
  let c := (u+u)+(u+u)
  let w := F ones ![e 0,(1 : M)+c+c]
  let z := F ones ![k,(1 : M)+(w+w)+(w+w)]
  have ho : F ones ![k+1,(1 : M)+(w+w)+(w+w)] = z+z+1 := by
    dsimp only [z]
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hin : modelWord (PA194SourceProgram.path 34)
      (F ones ![k+1,(1 : M)+(w+w)+(w+w)]+F ones ![k+1,(1 : M)+(w+w)+(w+w)]) =
      modelWord [true,false,false,true,false,false,false,false,true] z := by
    rw [PA194Path34Header.path34,ho]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  have h := PA194Site34SecondPass.secondPass k args
  dsimp only at h
  rw [hin] at h
  have hp := PA194Site34ThirdPrefix.prefixWord z
  simp only [modelNumeralOne] at hp
  dsimp only [secondClock]
  rw [PA194StepperCompose.modelStepperCompose,h,hp]
  simp only [modelNumeralOne,modelWord]
  rfl
#print axioms to1
end models
end PA194Site34ThirdTo1
