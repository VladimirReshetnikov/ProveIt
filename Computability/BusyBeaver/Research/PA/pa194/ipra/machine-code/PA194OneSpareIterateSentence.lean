import PA194OneSpareIterate
import PA194StartupSentence
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194OneSpareIterateSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194StateOne PA194StartupSentence PA194OneSpareIterate
abbrev T := TermN 3
def A (a b : T) : T := app2 addCode a b
def n : T := .bvar 0
def left : T := .bvar 1
def tail : T := .bvar 2
def c (j : Nat) : T := state j
def clock : T := A (A n n) n
def inputRight : T := app2 repeatBlock n tail
def outputLeft : T := app2 repeatBlock n left
def lhs : T := app2 PA194Stepper.stepper clock (PA194StartupSentence.pack (c 3) left inputRight)
def rhs : T := PA194StartupSentence.pack (c 3) outputLeft tail
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
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  apply (eqClosureModels _ _).mpr
  intro e
  have h := PA194OneSpareIterate.modelFullCarry (M := M) (e 0) (e 1) (e 2)
  simp only [lhs,rhs,clock,inputRight,outputLeft,PA194StartupSentence.pack,c,A,
    PA194StartupSentence.valApp2,valState,n,left,tail,Semiterm.val_bvar]
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
end PA194OneSpareIterateSentence
