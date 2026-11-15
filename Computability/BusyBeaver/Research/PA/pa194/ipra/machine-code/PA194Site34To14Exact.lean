import PA194Site34To113
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34To14Exact
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

theorem loop113 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![l,r+r+1]]) =
      F pairCode ![modelNumeral M 113,F pairCode ![l+l+1,r]] := by
  have h := rightOne 113 1 113 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne] using h

theorem to14 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let e := physicalArgs args
    let q := F ones ![e 1+1,F (fileCode 8) (fun i => e i.succ.succ)]
    let b := F ones ![k,modelNumeral M 400]
    let a1 := b+b+1
    let a2 := a1+a1+1
    let a3 := a2+a2
    let left := F ones ![e 0+1,a3]
    let c := F addCode ![F addCode ![modelNumeral M 13,n+1],(1 : M)]
    let first := F addCode ![F addCode ![c,(k+1)+1],modelNumeral M 23]
    let second := F addCode ![first,modelNumeral M 8]
    let third := F addCode ![F addCode ![second,k],modelNumeral M 3]
    F PA194Stepper.stepper ![F addCode ![third,(e 0+1)+1],
      PA194SourceSite31Physical.physicalFrame 34 n args] =
      F pairCode ![modelNumeral M 14,F pairCode ![left+left,q]] := by
  dsimp only
  let e := physicalArgs args
  let q := F ones ![e 1+1,F (fileCode 8) (fun i => e i.succ.succ)]
  let b := F ones ![k,modelNumeral M 400]
  let a1 := b+b+1
  let a2 := a1+a1+1
  let a3 := a2+a2
  let left := F ones ![e 0+1,a3]
  have hfile : F (fileCode 9) (fun i => e i.succ) = q+q := by
    rw [modelFileSucc,modelBlock]
    rfl
  have hp := PA194Site34To113.to113 k args
  dsimp only at hp
  rw [hfile] at hp
  have hscan := PA194GenericRightScan.modelFullScan 113 loop113 (e 0+1) a3 (q+q)
  have hrow := rightZero 113 0 14 (by decide) (by decide +kernel) left q
  simp only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] at hrow
  have hext : F PA194Stepper.stepper ![(e 0+1)+1,F pairCode ![modelNumeral M 113,
      F pairCode ![a3,F ones ![e 0+1,q+q]]]] = F pairCode ![modelNumeral M 14,F pairCode ![left+left,q]] := by
    change F PA194Stepper.stepper ![F addCode ![e 0+1,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc,hscan,hrow]
  rw [PA194StepperCompose.modelStepperCompose,hp,hext]
#print axioms loop113
#print axioms to14
end models
end PA194Site34To14Exact
