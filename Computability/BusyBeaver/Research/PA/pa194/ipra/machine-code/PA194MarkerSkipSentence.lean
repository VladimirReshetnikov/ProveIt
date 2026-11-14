import PA194MarkerSkip
import PA194IncrementReturnSentence
set_option autoImplicit false
namespace PA194MarkerSkipSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194MarkerScan PA194MarkerSkip PA194UnaryRuns PA194IncrementReturnSentence

def count : TermN 3 := app2 addCode one (app2 addCode #0 one)
def block : TermN 3 := PA194IncrementReturnSentence.twice (app2 addCode (PA194IncrementReturnSentence.twice (app2 ones #0 #2)) one)
def lhs (i : Fin 8) : TermN 3 := app2 PA194Stepper.stepper count
  (PA194IncrementReturnSentence.pack (state (markerControl i.succ)) #1 block)
def rhs (i : Fin 8) : TermN 3 := PA194IncrementReturnSentence.pack (state (markerControl i.castSucc))
  (app2 ones (app2 addCode #0 one) (PA194IncrementReturnSentence.twice #1)) #2
def sentence (i : Fin 8) : Sentence language := equalClosure (lhs i) (rhs i)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence (i : Fin 8) : M↓[language] ⊧ sentence i := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,count,block,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,
    valApp2,valState,valOne,Semiterm.val_bvar]
  exact modelMarkerSkipCell i (e 0) (e 1) (e 2)
end models
theorem classicalPRA (i : Fin 8) : PRA ⊢ sentence i := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence i
theorem nativeIPRA (i : Fin 8) : standardTheory ⊢ equalClosureI (lhs i) (rhs i) :=
  nativeOfClassical (lhs i) (rhs i) (classicalPRA i)
#print axioms modelSentence
#print axioms nativeIPRA
end PA194MarkerSkipSentence
