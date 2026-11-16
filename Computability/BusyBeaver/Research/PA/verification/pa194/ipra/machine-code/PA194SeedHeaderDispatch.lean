import PA194StartupSourceFrame
import PA194IncrementDispatch
import PA194LeftRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SeedHeaderDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StartupSourceFrame PA194IncrementDispatch PA194RightRows PA194LeftRows
open PA194BinaryDouble PA194ZeroRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem row34zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 34,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 44,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 34 0 44 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row44zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 44,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 62,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 44 0 62 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row62zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 62,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 87,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 62 0 87 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row65zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 65,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 91,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 65 0 91 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row91zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 91,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 110,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 91 0 110 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row110zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 110,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 59,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 110 0 59 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row87zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 87,F pairCode ![l+l,r+r]]) =
    F pairCode ![modelNumeral M 46,F pairCode ![l,(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero 87 46 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add] using h

theorem row46zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 46,F pairCode ![l+l,r+r]]) =
    F pairCode ![modelNumeral M 65,F pairCode ![l,(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero 46 65 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add] using h

theorem row59zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 59,F pairCode ![l+l,r+r]]) =
    F pairCode ![modelNumeral M 84,F pairCode ![l,(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero 59 84 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add] using h

/-- Source-root prefix for the seeded first-instruction route. The residual
header tail is arbitrary, including nonstandard model values. -/
theorem twelveSteps (l s : M) :
    let y0 := s+s
    let y1 := y0+y0
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    let y5 := y4+y4
    let y6 := y5+y5
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3
    let a5 := a4+a4
    F PA194Stepper.stepper ![modelNumeral M 12,F pairCode ![modelNumeral M 24,F pairCode ![l,y6+y6+1]]] =
    F pairCode ![modelNumeral M 84,F pairCode ![a5,y1]] := by
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 11),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 11 = F Code.succ (fun _ => modelNumeral M 10) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 10 = F Code.succ (fun _ => modelNumeral M 9) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 9 = F Code.succ (fun _ => modelNumeral M 8) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 8 = F Code.succ (fun _ => modelNumeral M 7) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 7 = F Code.succ (fun _ => modelNumeral M 6) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 6 = F Code.succ (fun _ => modelNumeral M 5) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 5 = F Code.succ (fun _ => modelNumeral M 4) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [row24,row26,row29,row34zero,row44zero,row62zero,row87zero,row46zero,row65zero,row91zero,row110zero,row59zero]

/-- A model-uniform source-header prefix composed with the fixed physical
blank startup. The seeded source file and every spare remain encoded. -/
theorem modelSeedAt84 :
    let f := F PA194RegisterPermutation.sourceFileCode (fun i => modelNumeral M (seedArgs i))
    let t := f+f+1
    let s := F zeros ![modelNumeral M 40,t]
    let a0 := modelNumeral M 1 + modelNumeral M 1 + 1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3
    let a5 := a4+a4
    F PA194Stepper.stepper ![modelNumeral M 58166,modelNumeral M 0] =
      F pairCode ![modelNumeral M 84,F pairCode ![a5,(s+s)+(s+s)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let f := F PA194RegisterPermutation.sourceFileCode (fun i => modelNumeral M (seedArgs i))
  let t := f+f+1
  let s := F zeros ![modelNumeral M 40,t]
  let y0 := s+s
  let y1 := y0+y0
  let y2 := y1+y1
  let y3 := y2+y2
  let y4 := y3+y3
  let y5 := y4+y4
  let y6 := y5+y5
  have h41 : F zeros ![modelNumeral M 41,t] = y0 := by
    change F zeros ![F Code.succ (fun _ => modelNumeral M 40),t] = _
    rw [modelZerosSucc]
  have h42 : F zeros ![modelNumeral M 42,t] = y1 := by
    change F zeros ![F Code.succ (fun _ => modelNumeral M 41),t] = _
    rw [modelZerosSucc,h41]
  have h43 : F zeros ![modelNumeral M 43,t] = y2 := by
    change F zeros ![F Code.succ (fun _ => modelNumeral M 42),t] = _
    rw [modelZerosSucc,h42]
  have h44 : F zeros ![modelNumeral M 44,t] = y3 := by
    change F zeros ![F Code.succ (fun _ => modelNumeral M 43),t] = _
    rw [modelZerosSucc,h43]
  have h45 : F zeros ![modelNumeral M 45,t] = y4 := by
    change F zeros ![F Code.succ (fun _ => modelNumeral M 44),t] = _
    rw [modelZerosSucc,h44]
  have h46 : F zeros ![modelNumeral M 46,t] = y5 := by
    change F zeros ![F Code.succ (fun _ => modelNumeral M 45),t] = _
    rw [modelZerosSucc,h45]
  have h47 : F zeros ![modelNumeral M 47,t] = y6 := by
    change F zeros ![F Code.succ (fun _ => modelNumeral M 46),t] = _
    rw [modelZerosSucc,h46]
  have hclock : modelNumeral M 58166 = F addCode ![modelNumeral M 58154,modelNumeral M 12] := by
    change modelNumeral M 58166 = modelNumeral M 58154 + modelNumeral M 12
    exact modelNumeralAdd 58154 12
  rw [hclock,PA194StepperCompose.modelStepperCompose,modelDenseStartupSourceFrame,h47]
  exact twelveSteps (modelNumeral M 1) s
#print axioms modelSeedAt84
#print axioms twelveSteps
end models
end PA194SeedHeaderDispatch
