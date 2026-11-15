import PA194Site34NinetyThree
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34To113
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194RightRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to113 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let e := physicalArgs args
    let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
    let b := F ones ![k,modelNumeral M 400]
    let a1 := b+b+1
    let a2 := a1+a1+1
    let a3 := a2+a2
    let c := F addCode ![F addCode ![modelNumeral M 13,n+1],(1 : M)]
    let first := F addCode ![F addCode ![c,(k+1)+1],modelNumeral M 23]
    let second := F addCode ![first,modelNumeral M 8]
    F PA194Stepper.stepper ![F addCode ![F addCode ![second,k],modelNumeral M 3],
      PA194SourceSite31Physical.physicalFrame 34 n args] =
      F pairCode ![modelNumeral M 113,F pairCode ![a3,p]] := by
  dsimp only
  let e := physicalArgs args
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let f := F sourceFileCode args
  let d := (1 : M)+(f+f)
  let v := (1 : M)+(d+d)
  let b := F ones ![k,modelNumeral M 400]
  have hf : f = p+p := by
    rw [show f = F (fileCode 10) e from modelSourceFile args,modelFileSucc,modelBlock]
  have hv : v = modelWord [true,true,false] p := by
    dsimp [v,d]
    rw [hf]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
    simp only [add_assoc,add_comm,add_left_comm]
  have h93 := PA194Site34To93.to93 k args
  dsimp only at h93
  have hs := PA194GenericRightScan.modelFullScan 93 PA194Site34NinetyThree.loop k (modelNumeral M 400) v
  have h4 := PA194Site34NinetyThree.threeRows b p
  dsimp only at h4
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h93,hs,hv,h4]
#print axioms to113
end models
end PA194Site34To113
