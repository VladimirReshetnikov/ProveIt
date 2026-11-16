import PA194Site31Sentence
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
namespace PA194Site31CodedClock
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PA194Site31Sentence PA194StartupSentence PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory

def total : T :=
  let t0 := clock24
  let t1 := A t0 (plus1 k)
  let t2 := A t1 cc6
  let t3 := A t2 front
  let t4 := A t3 one
  let t5 := A t4 (A (twice count) count)
  let t6 := A t5 (c 3)
  let t7 := A t6 (c 2)
  let t8 := A t7 (A (twice count) count)
  let t9 := A t8 cc3
  let t10 := A t9 (plus1 (plus1 (plus1 (E 0))))
  let t11 := A t10 cc6
  let t12 := A t11 (plus1 (plus1 k))
  let t13 := A t12 (c 2)
  let t14 := A t13 (plus1 (A (plus1 (c 2)) k))
  let t15 := A t14 (A (A one k) (c 3))
  let t16 := A t15 one
  let t17 := A t16 one
  A t17 (A (c 3) rc)

def clockCode : Code 13 := compileTerm total
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)

theorem codedRun (e : Fin 13 → M) (x : T) :
    F PA194Stepper.stepper ![F clockCode e, Semiterm.val e Empty.elim x] =
      Semiterm.val e Empty.elim (afterT (run clock24 x)) := by
  rw [clockCode,modelCompile]
  simp only [total,afterT,coreFor,run,A,valApp2,←PA194StepperCompose.modelStepperCompose]
theorem codedFrame (e : Fin 13 → M) :
    F PA194Stepper.stepper ![F clockCode e, Semiterm.val e Empty.elim (frame 31 input)] =
      Semiterm.val e Empty.elim (frame 32 output) := by
  rw [codedRun]
  exact (eqClosureModels _ _).mp (PA194Site31Sentence.modelSentence (M := M)) e
#print axioms codedRun
#print axioms codedFrame
end models
end PA194Site31CodedClock
