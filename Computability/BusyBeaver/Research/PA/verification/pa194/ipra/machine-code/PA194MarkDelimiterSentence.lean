import PA194MarkDelimiter
import PRAEqualityToIPRA
set_option autoImplicit false
namespace PA194MarkDelimiterSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PRAModelIOpenPairing PA194MarkDelimiter BinaryTapeCodes TableDispatch

def app1 {n : Nat} (f : Code 1) (a : TermN n) : TermN n := .func f ![a]
def app2 {n : Nat} (f : Code 2) (a b : TermN n) : TermN n := .func f ![a,b]
def one {n : Nat} : TermN n := .func oneCode Fin.elim0
def state {n : Nat} (q : Nat) : TermN n := .func (constantCode q) ![.func (.zero 0) Fin.elim0]
def pack {n : Nat} (q l r : TermN n) : TermN n := app2 pairCode q (app2 pairCode l r)
def twice {n : Nat} (x : TermN n) : TermN n := app2 addCode x x

def lhs : TermN 2 := app2 PA194Stepper.stepper (state 3)
  (pack (state 113) #0 (twice (app2 addCode (twice #1) one)))
def rhs : TermN 2 := pack (state 15) (app1 halfCode #0)
  (app2 addCode (app1 parityCode #0) (twice (twice (twice #1))))
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
theorem valApp2 {n : Nat} (e : Fin n → M) (f : Code 2) (a b : TermN n) :
    Semiterm.val e Empty.elim (app2 f a b) = F f ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  exact val_term_pair e a b

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp1 {n : Nat} (e : Fin n → M) (f : Code 1) (a : TermN n) :
    Semiterm.val e Empty.elim (app1 f a) = F f (fun _ => Semiterm.val e Empty.elim a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valOne {n : Nat} (e : Fin n → M) : Semiterm.val e Empty.elim one = (1 : M) := by
  simp only [one,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

theorem valState {n : Nat} (e : Fin n → M) (q : Nat) : Semiterm.val e Empty.elim (state q) = modelNumeral M q := by
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [state,Semiterm.val_func]
  have hv : (Semiterm.val e Empty.elim ∘ ![(.func (.zero 0) Fin.elim0 : TermN n)]) =
      (fun _ => (0 : M)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp [Semiterm.val_func,hz]
    rfl
  rw [hv]
  exact modelConstant q _

theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,pack,twice,
    valApp2,valApp1,valState,valOne,Semiterm.val_bvar]
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  change F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 113,
    F pairCode ![e 0,(e 1+e 1+1)+(e 1+e 1+1)]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => e 0),
      F parityCode (fun _ => e 0)+(((e 1+e 1)+(e 1+e 1))+((e 1+e 1)+(e 1+e 1)))]]
  simpa only [add_assoc] using modelMarkDelimiter (e 0) (e 1)
end models
theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence
theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs :=
  nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms nativeIPRA
end PA194MarkDelimiterSentence
