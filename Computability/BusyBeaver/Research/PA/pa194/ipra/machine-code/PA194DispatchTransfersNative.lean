import PA194FetchDecodeNative
import PA194DispatchTransfersOpen
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194DispatchTransfersNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194SourceControllerCode PA194SchedulerFetchPositive PA194DecoderNative PA194FetchDecodeNative PA194UnpairDrainOpenComplete
abbrev T := TermN 12
def raw : Fin 11 → T := fun i => .bvar ⟨i.val, by have h := i.isLt; omega⟩
def three (t : T) : T := app2 addCode (app2 addCode t t) t
def clock : T := app2 addCode (app2 addCode (three (raw 7)) one) (app2 addCode (three (raw 6)) one)
def out : Fin 11 → T := Function.update (Function.update (Function.update (Function.update raw 3 (app2 addCode (raw 3) (raw 6))) 6 zero) 7 zero) 8 (app2 addCode (raw 8) (raw 7))
def lhs : T := app2 PA194SourceControllerCode.run clock (frame 42 raw (.bvar 11))
def rhs : T := frame 48 out (.bvar 11)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelSentence : M↓[language] ⊧ equalClosure lhs rhs := by
  apply (eqClosureModels _ _).mpr
  intro e
  let initial : Fin 11 → M := fun i => e ⟨i.val, by have h:=i.isLt; omega⟩
  have h := (PA194DispatchTransfersOpen.transferToDispatch initial (e 11)).1
  simp [lhs,rhs,clock,three,raw,valApp1,valApp2,valFrame,valOne,Semiterm.val_bvar,
    PA194Transfer42Open.three,PA194Transfer45Open.three,initial] at h ⊢
  convert h using 1
  · rfl
  · apply congrArg (fun r => sourceState 48 r (e 11))
    funext i
    fin_cases i <;> simp [out,raw,initial,PA194Transfer42Open.argsAt,PA194Transfer45Open.argsAt,
      valApp1,valApp2,valZero,Semiterm.val_bvar,Function.update,subSelf] <;> first | rfl | exact (subSelf _).symm
end models

theorem classicalPRA : PRA ⊢ equalClosure lhs rhs := by
  apply Theory.Proof.complete_on_eq_models.{0,0}; intro M _ _ _ _; exact modelSentence
theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs := nativeOfClassical _ _ classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194DispatchTransfersNative
