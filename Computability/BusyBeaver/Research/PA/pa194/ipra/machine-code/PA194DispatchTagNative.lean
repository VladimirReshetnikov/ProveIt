import PA194DecoderNative
import PA194DispatchTag
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194DispatchTagNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194SourceControllerCode PA194SchedulerFetchPositive PA194DecoderNative PA194DispatchTag
abbrev T := TermN 12
def raw : Fin 11 → T := fun i => .bvar ⟨i.val, by have h := i.isLt; omega⟩
def zeroArgs : Fin 11 → T := Function.update raw 3 zero
def oneArgs : Fin 11 → T := Function.update raw 3 one
def axArgs : Fin 11 → T := Function.update raw 3 (app2 addCode (app2 addCode (.bvar 3) one) one)
def axOut : Fin 11 → T := Function.update raw 3 (.bvar 3)
def step1 (s : T) : T := app1 PA194SourceControllerCode.step s
def shiftLhs : T := step1 (frame 48 zeroArgs (.bvar 11))
def shiftRhs : T := frame 3661 zeroArgs (.bvar 11)
def mpLhs : T := step1 (step1 (frame 48 oneArgs (.bvar 11)))
def mpRhs : T := frame 3554 zeroArgs (.bvar 11)
def axLhs : T := step1 (step1 (frame 48 axArgs (.bvar 11)))
def axRhs : T := frame 50 axOut (.bvar 11)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem shiftModel : M↓[language] ⊧ equalClosure shiftLhs shiftRhs := by
  apply (eqClosureModels _ _).mpr
  intro e
  let initial : Fin 11 → M := fun i => Semiterm.val e Empty.elim (zeroArgs i)
  have h3 : initial 3 = (0 : M) := by simp [initial,zeroArgs,valZero]
  have h := PA194DispatchTag.shiftTag initial (e 11) h3
  simp [shiftLhs,shiftRhs,step1,zeroArgs,raw,frame,PA194DecoderNative.file,valApp1,valApp2,valState,valZero,valOne,Semiterm.val_bvar,modelPairCode,sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,initial,Function.update] at h ⊢
  convert h using 1 <;> rfl

theorem mpModel : M↓[language] ⊧ equalClosure mpLhs mpRhs := by
  apply (eqClosureModels _ _).mpr
  intro e
  let initial : Fin 11 → M := fun i => Semiterm.val e Empty.elim (oneArgs i)
  have h3 : initial 3 = (1 : M) := by simp [initial,oneArgs,valOne]
  have h := PA194DispatchTag.mpTag initial (e 11) h3
  simp [mpLhs,mpRhs,step1,oneArgs,zeroArgs,raw,frame,PA194DecoderNative.file,valApp1,valApp2,valState,valZero,valOne,Semiterm.val_bvar,modelPairCode,sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,initial,Function.update] at h ⊢
  convert h using 1 <;> rfl

theorem axModel : M↓[language] ⊧ equalClosure axLhs axRhs := by
  apply (eqClosureModels _ _).mpr
  intro e
  let initial : Fin 11 → M := fun i => Semiterm.val e Empty.elim (axArgs i)
  have h3 : initial 3 = (e 3+1)+1 := by
    simp [initial,axArgs,raw,valApp2,valOne,Semiterm.val_bvar]
    rfl
  have h := PA194DispatchTag.axTag initial (e 11) (e 3) h3
  simp [axLhs,axRhs,step1,axArgs,axOut,raw,frame,PA194DecoderNative.file,valApp1,valApp2,valState,valZero,valOne,Semiterm.val_bvar,modelPairCode,sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,initial,Function.update] at h ⊢
  convert h using 1 <;> rfl
end models

theorem shiftPRA : PRA ⊢ equalClosure shiftLhs shiftRhs := by
  apply Theory.Proof.complete_on_eq_models.{0,0}; intro M _ _ _ _; exact shiftModel

theorem mpPRA : PRA ⊢ equalClosure mpLhs mpRhs := by
  apply Theory.Proof.complete_on_eq_models.{0,0}; intro M _ _ _ _; exact mpModel

theorem axPRA : PRA ⊢ equalClosure axLhs axRhs := by
  apply Theory.Proof.complete_on_eq_models.{0,0}; intro M _ _ _ _; exact axModel

theorem shiftIPRA : standardTheory ⊢ equalClosureI shiftLhs shiftRhs := nativeOfClassical _ _ shiftPRA
theorem mpIPRA : standardTheory ⊢ equalClosureI mpLhs mpRhs := nativeOfClassical _ _ mpPRA
theorem axIPRA : standardTheory ⊢ equalClosureI axLhs axRhs := nativeOfClassical _ _ axPRA
#print axioms shiftModel
#print axioms mpModel
#print axioms axModel
#print axioms shiftPRA
#print axioms mpPRA
#print axioms axPRA
#print axioms shiftIPRA
#print axioms mpIPRA
#print axioms axIPRA
end PA194DispatchTagNative
