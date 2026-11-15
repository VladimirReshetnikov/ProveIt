import PA194SeedZeroThenPositive
import PA194Site28Complete
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SeedReach29
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StartupSourceFrame PA194ZeroThenPositive PA194SeedZeroThenPositive PA194Site28Complete PA194Site28SeedRoundTrip PA194Site28OutputFile PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem blankToSite29 :
    let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
    let k : M := modelNumeral M 39
    let a := Function.update e 0 (1 : M)
    let prior := F PA194Stepper.stepper ![clock27 k e,
      F PA194Stepper.stepper ![clock25 (k+1) e,
        F PA194Stepper.stepper ![modelNumeral M 58154,modelNumeral M 0]]]
    finishRun k a (seedRun (a 9) (F PA194Stepper.stepper ![rootClock k a,prior])) =
      PA194Site28Complete.frame 29 (k+1) (updated a) := by
  let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
  let k : M := modelNumeral M 39
  let a := Function.update e 0 (1 : M)
  have ht : a 10 = modelNumeral M seedTail := by
    change Function.update e 0 (1 : M) 10 = _
    rw [Function.update_of_ne (by decide)]
    rfl
  have hprev := PA194SeedZeroThenPositive.seededZeroThenPositive (M := M)
  change F PA194Stepper.stepper ![clock27 k e,
    F PA194Stepper.stepper ![clock25 (k+1) e,
      F PA194Stepper.stepper ![modelNumeral M 58154,modelNumeral M 0]]] =
    PA194Site28Complete.frame 28 ((k+1)+1) a at hprev
  have hnext := PA194Site28Complete.complete (M := M) k a ht
  exact (congrArg (fun x => finishRun k a (seedRun (a 9) (F PA194Stepper.stepper ![rootClock k a,x]))) hprev).trans hnext
theorem site29Register0 :
    let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
    let a := Function.update e 0 (1 : M)
    updated a 0 = (1 : M) := by
  simp [updated]

theorem site29Register8 :
    let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
    let a := Function.update e 0 (1 : M)
    updated a 8 = (1 : M) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp [updated,seedArgs]
  rfl
#print axioms site29Register0
#print axioms site29Register8
#print axioms blankToSite29
end models
end PA194SeedReach29
