import PA194UnifiedFetchNative
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194FetchDecodeNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194SourceControllerCode PA194SchedulerFetchPositive PA194DecoderNative
open PA194DecoderCompleteOpen PA194DecoderClock PA194TargetCantor PA194MachineProjections
abbrev T := TermN 12
abbrev initial := PA194UnifiedFetchNative.args
abbrev mid := PA194UnifiedFetchNative.out
abbrev firstClock := PA194UnifiedFetchNative.clock
def midFrame : T := frame 34 mid (.bvar 11)
def p : T := app2 addCode (app2 fixedCantor (mid 6) (mid 7)) (mid 8)
def out : Fin 11 → T := Function.update (Function.update (Function.update mid 6 (app1 fixedFirst p)) 7 (app1 fixedSecond p)) 8 zero
def secondClock : T := app2 addCode (app2 totalClock (mid 8) midFrame) one
def clock : T := app2 addCode firstClock secondClock
def lhs : T := app2 PA194SourceControllerCode.run clock (frame 25 initial (.bvar 11))
def rhs : T := frame 42 out (.bvar 11)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem valFrame (e : Fin 12 → M) (q : Nat) (r : Fin 11 → T) (t : T) :
  Semiterm.val e Empty.elim (frame q r t) = sourceState q (fun i => Semiterm.val e Empty.elim (r i)) (Semiterm.val e Empty.elim t) := by
  simp [frame,PA194DecoderNative.file,valApp1,valApp2,valState,modelPairCode,sourceState,PA194SourceRegisterRelation.pack,regsOfArgs]

theorem modelSentence : M↓[language] ⊧ equalClosure lhs rhs := by
  apply (eqClosureModels _ _).mpr
  intro e
  let middle : Fin 11 → M := fun i => Semiterm.val e Empty.elim (mid i)
  have hf := (eqClosureModels PA194UnifiedFetchNative.lhs PA194UnifiedFetchNative.rhs).mp
    (PA194UnifiedFetchNative.modelSentence (M := M)) e
  have hd := PA194DecoderCompleteOpen.decodeCode middle (e 11)
  simp only [PA194UnifiedFetchNative.lhs,PA194UnifiedFetchNative.rhs,valApp2,valFrame,Semiterm.val_bvar] at hf
  simp only [lhs,rhs,clock,secondClock,midFrame,valApp2,valFrame,valOne,Semiterm.val_bvar]
  change F (PA194IteratedSimulation.iterate PA194SourceControllerCode.step) ![_ + _,_] = _
  rw [PA194IterateAddOpen.iterateAdd]
  change F PA194SourceControllerCode.run ![_,F PA194SourceControllerCode.run ![_,_]] = _
  rw [hf]
  simp [out,p,valApp1,valApp2,valZero,PA194DecoderSynchronizationOpen.argsAt,middle,Function.update] at hd ⊢
  convert hd using 1
  · rfl
  · apply congrArg (fun r => sourceState 42 r (e 11))
    funext i
    fin_cases i <;> simp [valApp1,valApp2,valZero]
end models

theorem classicalPRA : PRA ⊢ equalClosure lhs rhs := by
  apply Theory.Proof.complete_on_eq_models.{0,0}; intro M _ _ _ _; exact modelSentence
theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs := nativeOfClassical _ _ classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194FetchDecodeNative
