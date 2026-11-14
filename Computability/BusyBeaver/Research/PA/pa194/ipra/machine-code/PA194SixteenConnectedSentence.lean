import PA194SixteenConnected
import PRAEqualityToIPRA
set_option autoImplicit false
namespace PA194SixteenConnectedSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open BinaryTapeCodes TableDispatch PA194TwelveScanInvariant PA194SixteenConnected PA194ZeroRuns PA194UnaryRuns

def app1 (f : Code 1) (a : TermN 5) : TermN 5 := .func f ![a]
def app2 (f : Code 2) (a b : TermN 5) : TermN 5 := .func f ![a,b]
def one : TermN 5 := .func oneCode Fin.elim0
def state (n : Nat) : TermN 5 := .func (constantCode n) ![.func (.zero 0) Fin.elim0]
def pack (q l r : TermN 5) : TermN 5 := app2 pairCode q (app2 pairCode l r)
def twice (x : TermN 5) : TermN 5 := app2 addCode x x
def block : TermN 5 := app2 ones (app2 addCode #1 one) (twice #4)
def blockU : TermN 5 := app2 zeros #0 (app2 zeros #1 (app2 addCode (app2 addCode one (twice #4)) (twice #4)))
def blockV : TermN 5 := app2 ones #2 #3
def lhs : TermN 5 := app2 PA194Stepper.stepper
  (app2 addCode (app2 addCode (app2 addCode (app2 addCode (app2 addCode (app2 addCode (app2 addCode
    (app2 addCode (app2 addCode #0 one) (app2 addCode #1 one)) one) one) #1) #0) one) one) #2)
  (pack (state 12) (app2 addCode (twice (app2 addCode (twice blockV) one)) one)
    (app2 zeros #0 (app2 addCode (twice block) one)))
def rhs : TermN 5 := pack (state 16) #3
  (app2 ones (app2 addCode #2 one) (app2 addCode (app2 addCode one (twice blockU)) (twice blockU)))
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
 theorem valApp2 (e : Fin 5 → M) (f : Code 2) (a b : TermN 5) :
    Semiterm.val e Empty.elim (app2 f a b) = F f ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun k => Fin.elim0 k) j

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
 theorem valApp1 (e : Fin 5 → M) (f : Code 1) (a : TermN 5) :
    Semiterm.val e Empty.elim (app1 f a) = F f (fun _ => Semiterm.val e Empty.elim a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

theorem valState (e : Fin 5 → M) (n : Nat) : Semiterm.val e Empty.elim (state n) = modelNumeral M n := by
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 5)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [state,Semiterm.val_func]
  have hv : (Semiterm.val e Empty.elim ∘ ![(.func (.zero 0) Fin.elim0 : TermN 5)]) =
      (fun _ => (0 : M)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp [Semiterm.val_func,hz]
    rfl
  rw [hv]
  exact modelConstant n _

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valOne (e : Fin 5 → M) : Semiterm.val e Empty.elim one = (1 : M) := by
  simp only [one,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,pack,twice,block,blockU,blockV,valApp2,valState,valOne,Semiterm.val_bvar]
  exact modelConnectedSixteen (e 0) (e 1) (e 2) (e 3) (e 4)
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
end PA194SixteenConnectedSentence
