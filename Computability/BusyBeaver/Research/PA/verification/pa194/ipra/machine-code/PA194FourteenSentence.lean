import PA194FourteenComposition
import PRAEqualityToIPRA
set_option autoImplicit false
namespace PA194FourteenSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open BinaryTapeCodes TableDispatch PA194TwelveScanInvariant PA194FourteenComposition PA194ZeroRuns PA194UnaryRuns

def app1 (f : Code 1) (a : TermN 4) : TermN 4 := .func f ![a]
def app2 (f : Code 2) (a b : TermN 4) : TermN 4 := .func f ![a,b]
def one : TermN 4 := .func oneCode Fin.elim0
def state (n : Nat) : TermN 4 := .func (constantCode n) ![.func (.zero 0) Fin.elim0]
def pack (q l r : TermN 4) : TermN 4 := app2 pairCode q (app2 pairCode l r)
def twice (x : TermN 4) : TermN 4 := app2 addCode x x
def block : TermN 4 := app2 ones #1 (twice #3)
def zblock : TermN 4 := app2 zeros #1 (twice (app2 zeros #0 #2))
def lhs : TermN 4 := app2 PA194Stepper.stepper (app2 addCode (app2 addCode (app2 addCode (app2 addCode #0 one) #1) one) one)
  (pack (state 12) #2 (app2 zeros #0 (app2 addCode (twice block) one)))
def rhs : TermN 4 := pack (state 15) (app1 halfCode (app1 halfCode zblock))
  (app2 addCode (app2 addCode (app2 addCode (app1 parityCode (app1 halfCode zblock))
    (app2 addCode one one)) (twice (twice #3))) (twice (twice #3)))
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
 theorem valApp2 (e : Fin 4 → M) (f : Code 2) (a b : TermN 4) :
    Semiterm.val e Empty.elim (app2 f a b) = F f ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun k => Fin.elim0 k) j

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
 theorem valApp1 (e : Fin 4 → M) (f : Code 1) (a : TermN 4) :
    Semiterm.val e Empty.elim (app1 f a) = F f (fun _ => Semiterm.val e Empty.elim a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

theorem valState (e : Fin 4 → M) (n : Nat) : Semiterm.val e Empty.elim (state n) = modelNumeral M n := by
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 4)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [state,Semiterm.val_func]
  have hv : (Semiterm.val e Empty.elim ∘ ![(.func (.zero 0) Fin.elim0 : TermN 4)]) =
      (fun _ => (0 : M)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp [Semiterm.val_func,hz]
    rfl
  rw [hv]
  exact modelConstant n _

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valOne (e : Fin 4 → M) : Semiterm.val e Empty.elim one = (1 : M) := by
  simp only [one,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,pack,twice,block,zblock,valApp2,valApp1,valState,valOne,Semiterm.val_bvar]
  exact modelConnectedFifteen (e 0) (e 1) (e 2) (e 3)
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
end PA194FourteenSentence
