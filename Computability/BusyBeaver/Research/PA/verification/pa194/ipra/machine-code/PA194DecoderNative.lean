import PA194DecoderCompleteOpen
import PRAEqualityToIPRA
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194DecoderNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194SourceControllerCode PA194SchedulerFetchPositive PA194DecoderSynchronizationOpen
open PA194DecoderClock PA194DecoderCompleteOpen PA194TargetCantor PA194MachineProjections
abbrev T := TermN 12
def app1 (f : Code 1) (a : T) : T := .func f ![a]
def app2 (f : Code 2) (a b : T) : T := .func f ![a,b]
def zero : T := .func (.zero 0) Fin.elim0
def one : T := .func oneCode Fin.elim0
def state (q : Nat) : T := app1 (constantCode q) zero
def inputs : Fin 11 → T := fun i => .bvar ⟨i.val,by have h:=i.isLt; omega⟩
def file (r : Fin 11 → T) (tail : T) : T :=
  app2 pairCode (r 0) (app2 pairCode (r 1) (app2 pairCode (r 2) (app2 pairCode (r 3) (app2 pairCode (r 4)
    (app2 pairCode (r 5) (app2 pairCode (r 6) (app2 pairCode (r 7) (app2 pairCode (r 8) tail))))))))
def frame (q : Nat) (r : Fin 11 → T) (tail : T) : T := app2 pairCode (state q) (file r tail)
def start : T := frame 34 inputs (.bvar 11)
def p : T := app2 addCode (app2 fixedCantor (inputs 6) (inputs 7)) (inputs 8)
def out : Fin 11 → T := Function.update (Function.update (Function.update inputs 6 (app1 fixedFirst p)) 7 (app1 fixedSecond p)) 8 zero
def clock : T := app2 addCode (app2 totalClock (inputs 8) start) one
def lhs : T := app2 PA194SourceControllerCode.run clock start
def rhs : T := frame 42 out (.bvar 11)
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

theorem valApp1 (e : Fin 12 → M) (f : Code 1) (a : T) :
    Semiterm.val e Empty.elim (app1 f a) = F f ![Semiterm.val e Empty.elim a] := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i; fin_cases i; rfl

theorem valApp2 (e : Fin 12 → M) (f : Code 2) (a b : T) :
    Semiterm.val e Empty.elim (app2 f a b) = F f ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  funext i; fin_cases i <;> rfl

theorem valZero (e : Fin 12 → M) : Semiterm.val e Empty.elim zero = (0 : M) := by
  simp only [zero,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _
theorem valOne (e : Fin 12 → M) : Semiterm.val e Empty.elim one = (1 : M) := by
  simp only [one,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _
theorem valState (e : Fin 12 → M) (q : Nat) : Semiterm.val e Empty.elim (state q) = modelNumeral M q := by
  rw [state,valApp1,valZero]
  have hv : (![0] : Fin 1 → M) = (fun _ => (0 : M)) := by funext i; fin_cases i; rfl
  rw [hv]
  exact modelConstant q 0

theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  let initial : Fin 11 → M := fun i => e ⟨i.val,by have h:=i.isLt; omega⟩
  have h := PA194DecoderCompleteOpen.decodeCode initial (e 11)
  simp [lhs,rhs,clock,start,frame,file,p,inputs,out,valApp1,valApp2,valState,valZero,valOne,
    Semiterm.val_bvar,modelPairCode,sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,
    PA194DecoderSynchronizationOpen.argsAt,initial,Function.update] at h ⊢
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
end PA194DecoderNative
