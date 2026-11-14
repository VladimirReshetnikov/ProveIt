import PA194ReturnCell
import PRAEqualityToIPRA
set_option autoImplicit false
namespace PA194ReturnCellSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open BinaryTapeCodes TableDispatch PA194SixScanInvariant PA194ReturnCell PA194UnaryRuns

def app2 (f : Code 2) (a b : TermN 3) : TermN 3 := .func f ![a,b]
def app1 (f : Code 1) (a : TermN 3) : TermN 3 := .func f ![a]
def one : TermN 3 := .func oneCode Fin.elim0
def state (n : Nat) : TermN 3 := .func (constantCode n) ![.func (.zero 0) Fin.elim0]
def pack (q l r : TermN 3) : TermN 3 := app2 pairCode q (app2 pairCode l r)
def twice (x : TermN 3) : TermN 3 := app2 addCode x x
def block : TermN 3 := app2 ones #0 (app2 addCode (app2 addCode one #2) #2)
def lhs : TermN 3 := app2 PA194Stepper.stepper (app2 addCode (app2 addCode #0 one) one)
  (pack (state 7) (app2 ones #0 (twice #1)) (app2 addCode (twice #2) one))
def rhs : TermN 3 := pack (state 7) (app1 halfCode #1)
  (app2 addCode (app2 addCode (app1 parityCode #1) (twice block)) (twice block))
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
 theorem valApp2 (e : Fin 3 → M) (f : Code 2) (a b : TermN 3) :
    Semiterm.val e Empty.elim (app2 f a b) = F f ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  exact PA194SixScanInvariant.valClosed2 e f a b

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
 theorem valApp1 (e : Fin 3 → M) (f : Code 1) (a : TermN 3) :
    Semiterm.val e Empty.elim (app1 f a) = F f (fun _ => Semiterm.val e Empty.elim a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

theorem valState (e : Fin 3 → M) (n : Nat) : Semiterm.val e Empty.elim (state n) = modelNumeral M n := by
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 3)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [state,Semiterm.val_func]
  have hv : (Semiterm.val e Empty.elim ∘ ![(.func (.zero 0) Fin.elim0 : TermN 3)]) =
      (fun _ => (0 : M)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp [Semiterm.val_func,hz]
    rfl
  rw [hv]
  exact modelConstant n _

theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,pack,twice,block,valApp2,valApp1,valState,one,
    PA194SixScanInvariant.valClosedOne,Semiterm.val_bvar]
  exact modelReturnCell (e 0) (e 1) (e 2)
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
end PA194ReturnCellSentence
