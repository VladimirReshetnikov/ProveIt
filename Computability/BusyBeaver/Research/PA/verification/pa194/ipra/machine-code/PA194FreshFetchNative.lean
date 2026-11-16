import PA194DecoderNative
import PA194SourceFetchOpen
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194FreshFetchNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194SourceControllerCode PA194SchedulerFetchPositive PA194DecoderNative PA194SourceFetchOpen
abbrev T := TermN 12
def raw : Fin 11 → T := fun i => .bvar ⟨i.val,by have h:=i.isLt; omega⟩
def args : Fin 11 → T := Function.update (Function.update raw 6 zero) 8 zero
def n : T := args 0
def four : T := app2 addCode (app2 addCode n n) (app2 addCode n n)
def three : T := app2 addCode (app2 addCode n n) n
def clock : T := app2 addCode one (app2 addCode (app2 addCode four one) (app2 addCode (app2 addCode three one) one))
def out : Fin 11 → T := Function.update (Function.update args 0 (app2 addCode n one)) 8 n
def lhs : T := app2 PA194SourceControllerCode.run clock (frame 25 args (.bvar 11))
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
  have h6 : initial 6 = (0 : M) := by simp [initial,args,PA194DecoderNative.valZero]
  have h8 : initial 8 = (0 : M) := by simp [initial,args,PA194DecoderNative.valZero]
  have h := PA194SourceFetchOpen.freshSourceFetch initial (e 11) h8 h6
  simp [lhs,rhs,clock,four,three,n,out,args,raw,PA194DecoderNative.frame,PA194DecoderNative.file,
    PA194DecoderNative.valApp1,PA194DecoderNative.valApp2,PA194DecoderNative.valState,
    PA194DecoderNative.valZero,PA194DecoderNative.valOne,Semiterm.val_bvar,modelPairCode,
    sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,PA194SourceDrainOpen.four,
    PA194SourceRestoreOpen.three,initial,Function.update] at h ⊢
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
end PA194FreshFetchNative
