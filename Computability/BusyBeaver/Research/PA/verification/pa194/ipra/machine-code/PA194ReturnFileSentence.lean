import PA194ReturnFile
import PRAEqualityToIPRA
set_option autoImplicit false
namespace PA194ReturnFileSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194RegisterFile PA194ReturnFile PA194CarryFile TableDispatch

def app2 {n : Nat} (f : Code 2) (a b : TermN n) : TermN n := .func f ![a,b]
def one {n : Nat} : TermN n := .func oneCode Fin.elim0
def state {n : Nat} (q : Nat) : TermN n := .func (constantCode q) ![.func (.zero 0) Fin.elim0]
def pack {n : Nat} (q l r : TermN n) : TermN n := app2 pairCode q (app2 pairCode l r)
def twice {n : Nat} (x : TermN n) : TermN n := app2 addCode x x

def fileArgs (n : Nat) : Fin (n+1) → TermN (n+3) := fun i => .bvar i.succ.succ
def leftArgs (n : Nat) : Fin (n+2) → TermN (n+3) := Fin.cases #0 (fileArgs n)
def rightArgs (n : Nat) : Fin (n+2) → TermN (n+3) := Fin.cases #1 (fileArgs n)
def resultTail (n : Nat) : TermN (n+3) := .func (returnCode n) (rightArgs n)
def lhs (n : Nat) : TermN (n+3) := app2 PA194Stepper.stepper
    (.func (costCode n) (fileArgs n))
    (pack (state 7) (.func (leftCode n) (leftArgs n)) (app2 addCode (twice #1) one))
def rhs (n : Nat) : TermN (n+3) := pack (state 7) #0 (app2 addCode (twice (resultTail n)) one)
def sentence (n : Nat) : Sentence language := equalClosure (lhs n) (rhs n)

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

theorem modelSentence (n : Nat) : M↓[language] ⊧ sentence n := by
  apply (eqClosureModels _ _).mpr
  intro e
  let es : Fin (n+1) → M := fun i => e i.succ.succ
  have h := modelReturnFile n es (e 0) (e 1)
  have hl : (fun i : Fin (n+2) => Semiterm.val e Empty.elim (leftArgs n i)) = Fin.cases (e 0) es := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hr : (fun i : Fin (n+2) => Semiterm.val e Empty.elim (rightArgs n i)) = Fin.cases (e 1) es := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simp only [lhs,rhs,pack,twice,resultTail,fileArgs,valApp2,valState,valOne,Semiterm.val_bvar,
    Semiterm.val_func,Function.comp_def]
  rw [hl,hr]
  exact h
end models

theorem classicalPRA (n : Nat) : PRA ⊢ sentence n := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence n

theorem nativeIPRA (n : Nat) : standardTheory ⊢ equalClosureI (lhs n) (rhs n) :=
  nativeOfClassical (lhs n) (rhs n) (classicalPRA n)
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194ReturnFileSentence
