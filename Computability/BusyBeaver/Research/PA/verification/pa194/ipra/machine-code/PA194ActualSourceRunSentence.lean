import PA194ActualSourceRun
import PA194StartupSentence
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194ActualSourceRunSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction PackedDecoderModel PA194GenericRightScan PA194Site28CarryCell PA194Stepper PA194ModelLoopIteration PA194ModelSourceLoop PA194ActualSourceLoop PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes TableDispatch
open PA194StartupSentence PA194SourceControllerCode
abbrev T := TermN 10
def A (a b : T) : T := app2 addCode a b
def p (a b : T) : T := app2 pairCode a b
def r (i : Fin 9) : T := .bvar ⟨i.val,by have h := i.isLt; omega⟩
def tail : T := .bvar 9
def sourceT (reg : Fin 9 → T) : T :=
  p (state 27) (p (reg 0) (p (reg 1) (p (reg 2) (p (reg 3) (p (reg 4) (p (reg 5) (p (reg 6) (p (reg 7) (p (reg 8) tail)))))))))
def out : Fin 9 → T := ![zero,r 1,r 2,r 3,r 4,r 5,A (r 6) (r 0),r 7,A (r 8) (r 0)]
def clock : T := A (A (r 0) (r 0)) (A (r 0) (r 0))
def lhs : T := app2 PA194SourceControllerCode.run clock (sourceT r)
def rhs : T := sourceT out
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
  have hz : F subCode ![rs 0,rs 0] = (0 : M) := by rw [modelSubAsTsub]; simp
  have hout : PA194ModelSourceLoop.running rs (rs 0) =
      Function.update (Function.update (Function.update rs 0 (0 : M)) 6 (rs 6+rs 0)) 8 (rs 8+rs 0) := by
    funext i
    fin_cases i <;> simp [PA194ModelSourceLoop.running,hz]
  have h := (PA194ActualSourceRun.reachesZero rs (e 9)).1
  rw [hout] at h
  simp [PA194ModelSourceLoop.source,Function.update] at h
  simp [lhs,rhs,clock,sourceT,p,A,out,r,tail,PA194StartupSentence.valApp2,PA194StartupSentence.valState,PA194StartupSentence.valZero,Semiterm.val_bvar,modelPairCode]
  exact h
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
end PA194ActualSourceRunSentence
