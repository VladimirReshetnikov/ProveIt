import PA194DecrementPositiveCell
import PA194IncrementReturnSentence
set_option autoImplicit false
namespace PA194DecrementPositiveCellSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194DecrementPositiveCell BinaryTapeCodes TableDispatch PA194IncrementReturnSentence

def a : TermN 2 := app2 addCode (PA194IncrementReturnSentence.twice #1) one
def b : TermN 2 := PA194IncrementReturnSentence.twice a
def right : TermN 2 := PA194IncrementReturnSentence.twice b
def lhs : TermN 2 := app2 PA194Stepper.stepper (state 4) (PA194IncrementReturnSentence.pack (state 1) #0 right)
def rhs : TermN 2 := PA194IncrementReturnSentence.pack (state 7) #0 (app2 addCode right one)
def sentence : Sentence language := equalClosure lhs rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,right,b,a,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,
    valApp2,valState,valOne,Semiterm.val_bvar,PA194StateOne.modelNumeralOne]
  exact modelPositiveCell (e 0) (e 1)
end models
theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence
theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs :=
  nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms nativeIPRA
end PA194DecrementPositiveCellSentence
