import PA194ActualPhysicalOrbitCode
import PA194StartupSentence
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable section
namespace PA194ActualPhysicalOrbitSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualLoopOrbit PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header PA194StartupSentence
abbrev T := TermN 13
def A (a b : T) : T := app2 addCode a b
def p (a b : T) : T := app2 pairCode a b
def r (i : Fin 9) : T := .bvar ⟨i.val,by have h := i.isLt; omega⟩
def tail : T := .bvar 9
def k : T := .bvar 10
def n : T := .bvar 11
def spare : T := .bvar 12
def sourceT (reg : Fin 9 → T) : T :=
  p (state 27) (p (reg 0) (p (reg 1) (p (reg 2) (p (reg 3) (p (reg 4) (p (reg 5) (p (reg 6) (p (reg 7) (p (reg 8) tail)))))))))
def pack (g count s control : T) : T := p g (p count (p s control))
def gap : T := A (A (A k one) one) one
def resultRegs : Fin 9 → T := ![app2 subCode (r 0) (r 0),r 1,r 2,r 3,r 4,r 5,A (r 6) (r 0),r 7,A (r 8) (r 0)]
def input : T := pack gap n spare (sourceT r)
def output : T := pack (A gap (r 0)) (A (A n (r 0)) (r 0)) spare (sourceT resultRegs)
def cost : Code 1 := loopCost PA194Site27ClockDirect.clockCode PA194Site28ClockCode.clockCode PA194Site29ClockCode.clockCode PA194ControllerLoopFrame.readers
def frame : Code 1 := PA194ModelLoopFrame.frame PA194ControllerLoopFrame.readers
def unaryTerm (c : Code 1) (x : T) : T := .func c ![x]
def lhs : T := app2 PA194Stepper.stepper (app2 (timeCode (PA194ModelLoopState.next quad) cost) (r 0) input) (unaryTerm frame input)
def rhs : T := unaryTerm frame output
def sentence : Sentence language := equalClosure lhs rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  apply (eqClosureModels _ _).mpr
  intro e
  let rs : Fin 9 → M := fun i => e ⟨i.val,by have h := i.isLt; omega⟩
  have h := PA194ActualPhysicalOrbitCode.completeLoop rs (e 9) (e 10) (e 11) (e 12)
  dsimp only at h
  simp [lhs,rhs,input,output,pack,sourceT,p,A,gap,k,n,spare,tail,r,resultRegs,unaryTerm,cost,frame,
    PA194StartupSentence.valApp2,PA194StartupSentence.valState,PA194StartupSentence.valOne,
    Semiterm.val_bvar,Semiterm.val_func,Function.comp_def,PA194ModelLoopState.packed,
    PA194ModelSourceLoop.source,PA194ModelSourceLoop.running,Function.update,modelPairCode] at h ⊢
  exact h
end models
theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence
theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs := nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194ActualPhysicalOrbitSentence
