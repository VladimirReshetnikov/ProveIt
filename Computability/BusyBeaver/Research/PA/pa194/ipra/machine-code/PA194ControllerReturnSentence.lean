import PA194ControllerReturn
import PA194IncrementReturnSentence
set_option autoImplicit false
namespace PA194ControllerReturnSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194ControllerReturn PA194MarkerReturnCell PA194UnaryRuns BinaryTapeCodes PA194IncrementReturnSentence

def markerRight : TermN 3 := app2 addCode (twice #2) one
def aTerm : TermN 3 := app2 ones #0 (app2 addCode one (twice #2))
def leftTerm : TermN 3 := app2 ones #0 (twice (twice #1))
def clockTerm : TermN 3 := app2 addCode (app2 addCode (app2 addCode #0 one) one) one
def lhs (i : Fin 2) : TermN 3 := app2 PA194Stepper.stepper clockTerm
  (PA194IncrementReturnSentence.pack (state (returnControl i)) leftTerm markerRight)
def rhs : TermN 3 := PA194IncrementReturnSentence.pack (state 18) (app1 halfCode #1)
  (app2 addCode (app1 parityCode #1) (twice (twice (twice aTerm))))
def sentence (i : Fin 2) : Sentence language := equalClosure (lhs i) rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence (i : Fin 2) : M↓[language] ⊧ sentence i := by
  apply (eqClosureModels _ _).mpr
  intro e
  have h := modelReturnToControl18 i (e 0) (e 1) (e 2)
  dsimp only at h
  simp only [lhs,rhs,clockTerm,markerRight,leftTerm,aTerm,PA194IncrementReturnSentence.pack,twice,
    valApp2,valApp1,valState,valOne,Semiterm.val_bvar,Semiterm.val_func,Function.comp_def]
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  change F PA194Stepper.stepper ![((e 0+1)+1)+1,
    F pairCode ![TableDispatch.modelNumeral M (returnControl i),F pairCode ![
      F ones ![e 0,(e 1+e 1)+(e 1+e 1)],(e 2+e 2)+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 18,F pairCode ![F halfCode (fun _ => e 1),
      F parityCode (fun _ => e 1)+(
      ((F ones ![e 0,1+(e 2+e 2)]+F ones ![e 0,1+(e 2+e 2)])+
       (F ones ![e 0,1+(e 2+e 2)]+F ones ![e 0,1+(e 2+e 2)]))+
      ((F ones ![e 0,1+(e 2+e 2)]+F ones ![e 0,1+(e 2+e 2)])+
       (F ones ![e 0,1+(e 2+e 2)]+F ones ![e 0,1+(e 2+e 2)])))]]
  simpa only [add_assoc] using h
end models
theorem classicalPRA (i : Fin 2) : PRA ⊢ sentence i := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence i
theorem nativeIPRA (i : Fin 2) : standardTheory ⊢ equalClosureI (lhs i) rhs :=
  nativeOfClassical (lhs i) rhs (classicalPRA i)
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194ControllerReturnSentence
