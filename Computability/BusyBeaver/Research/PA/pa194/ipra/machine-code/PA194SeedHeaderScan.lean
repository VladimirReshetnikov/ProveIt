import PA194SeedHeaderDispatch
import PA194EightyFourScan
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SeedHeaderScan
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StartupSourceFrame PA194SeedHeaderDispatch PA194EightyFourScan
open PA194ZeroRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- After the seed header prefix, state 84 scans the remaining 42 zeros and
its delimiter into state 15, preserving the complete arbitrary model file. -/
theorem modelSeedAt15 :
    let f := F PA194RegisterPermutation.sourceFileCode (fun i => modelNumeral M (seedArgs i))
    let l := modelNumeral M 1
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3
    let a5 := a4+a4
    let a := F PA194UnaryRuns.ones ![modelNumeral M 42,a5]
    F PA194Stepper.stepper ![modelNumeral M 58209,modelNumeral M 0] =
      F pairCode ![modelNumeral M 15,F pairCode ![F BinaryTapeCodes.halfCode (fun _ => a),
        F BinaryTapeCodes.parityCode (fun _ => a)+(1+1)+(f+f)+(f+f)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let f := F PA194RegisterPermutation.sourceFileCode (fun i => modelNumeral M (seedArgs i))
  let t := f+f+1
  let s := F zeros ![modelNumeral M 40,t]
  have h41 : F zeros ![modelNumeral M 41,t] = s+s := by
    change F zeros ![F Code.succ (fun _ => modelNumeral M 40),t] = _
    rw [modelZerosSucc]
  have h42 : F zeros ![modelNumeral M 42,t] = (s+s)+(s+s) := by
    change F zeros ![F Code.succ (fun _ => modelNumeral M 41),t] = _
    rw [modelZerosSucc,h41]
  have h84 := modelSeedAt84 (M := M)
  dsimp only at h84
  rw [←h42] at h84
  have hclock : modelNumeral M 58209 = F addCode ![modelNumeral M 58166,modelNumeral M 42+1] := by
    change modelNumeral M 58209 = modelNumeral M 58166 + (modelNumeral M 42 + 1)
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [hclock,PA194StepperCompose.modelStepperCompose,h84]
  exact scanExit (modelNumeral M 42) _ f
#print axioms modelSeedAt15
end models
end PA194SeedHeaderScan
