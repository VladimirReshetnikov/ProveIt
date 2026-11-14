import PA194IncrementTail
import PRAEqualityToIPRA
set_option autoImplicit false
namespace PA194IncrementTailSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open BinaryTapeCodes TableDispatch PA194IncrementTail PA194StateOne

def app2 (f : Code 2) (a b : TermN 1) : TermN 1 := .func f ![a,b]
def one : TermN 1 := .func oneCode Fin.elim0
def state (n : Nat) : TermN 1 := .func (constantCode n) ![.func (.zero 0) Fin.elim0]
def pack (q l r : TermN 1) : TermN 1 := app2 pairCode q (app2 pairCode l r)
def twice (x : TermN 1) : TermN 1 := app2 addCode x x
def zero : TermN 1 := .func (Code.zero 0) Fin.elim0
def c3 : TermN 1 := app2 addCode (app2 addCode one one) one
def c13 : TermN 1 := app2 addCode (twice (twice c3)) one
def lhs : TermN 1 := app2 PA194Stepper.stepper (state 6) (pack (state 1) #0 zero)
def rhs : TermN 1 := pack (state 7) #0 c13
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

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp2 (e : Fin 1 → M) (f : Code 2) (a b : TermN 1) :
    Semiterm.val e Empty.elim (app2 f a b) = F f ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  exact val_term_pair e a b

theorem valState (e : Fin 1 → M) (n : Nat) : Semiterm.val e Empty.elim (state n) = modelNumeral M n := by
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [state,Semiterm.val_func]
  have hv : (Semiterm.val e Empty.elim ∘ ![(.func (.zero 0) Fin.elim0 : TermN 1)]) =
      (fun _ => (0 : M)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp [Semiterm.val_func,hz]
    rfl
  rw [hv]
  exact modelConstant n _

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valOne (e : Fin 1 → M) : Semiterm.val e Empty.elim one = (1 : M) := by
  simp only [one,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valZero (e : Fin 1 → M) : Semiterm.val e Empty.elim zero = (0 : M) := by
  simp only [zero,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,pack,twice,c3,c13,valApp2,valState,valOne,valZero,Semiterm.val_bvar,PA194StateOne.modelNumeralOne]
  exact modelAppendTail (e 0)
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
end PA194IncrementTailSentence
