import PA194DecoderNative
import PA194SchedulerFetchOpen
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194PositiveFetchNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194SourceControllerCode PA194SchedulerFetchPositive PA194DecoderNative PA194SchedulerFetchOpen
abbrev T := TermN 12
def raw : Fin 11 → T := fun i => .bvar ⟨i.val,by have h:=i.isLt; omega⟩
def args : Fin 11 → T := Function.update raw 8 (app2 addCode (.bvar 8) one)
def out : Fin 11 → T := Function.update args 8 (.bvar 8)
def lhs : T := app2 PA194SourceControllerCode.run (app2 addCode one one) (frame 25 args (.bvar 11))
def rhs : T := frame 34 out (.bvar 11)
def sentence : Sentence language := equalClosure lhs rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  let initial : Fin 11 → M := fun i => Semiterm.val e Empty.elim (args i)
  have h8 : initial 8 = e 8+(1 : M) := by
    simp [initial,args,raw,PA194DecoderNative.valApp2,PA194DecoderNative.valOne,Semiterm.val_bvar]
    rfl
  have h := (PA194SchedulerFetchPositive.positiveFetchPrefix initial (e 11) (e 8) h8).1
  have hrun : F PA194SourceControllerCode.run ![(1 : M)+1,sourceState 25 initial (e 11)] =
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![sourceState 25 initial (e 11)]] := by
    change F (PA194IteratedSimulation.iterate PA194SourceControllerCode.step) ![(1 : M)+1,sourceState 25 initial (e 11)] = _
    have hz : (1 : M)+1 = ((0 : M)+1)+1 := by rw [zero_add]
    rw [hz,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterZero]
  rw [←hrun] at h
  simp [lhs,rhs,args,raw,out,PA194DecoderNative.frame,PA194DecoderNative.file,
    PA194DecoderNative.valApp1,PA194DecoderNative.valApp2,PA194DecoderNative.valState,
    PA194DecoderNative.valZero,PA194DecoderNative.valOne,Semiterm.val_bvar,modelPairCode,
    sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,initial,Function.update] at h ⊢
  convert h using 1 <;> rfl
end models

theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence

theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs :=
  nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194PositiveFetchNative
