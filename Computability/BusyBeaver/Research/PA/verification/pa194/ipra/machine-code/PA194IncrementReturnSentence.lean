import PA194IncrementReturn
import PRAEqualityToIPRA
set_option autoImplicit false
namespace PA194IncrementReturnSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194RegisterFile PA194IncrementReturn PA194MarkedFile PA194CarryFile PA194ReturnFile PA194UnaryRuns BinaryTapeCodes TableDispatch

def app1 {n : Nat} (f : Code 1) (a : TermN n) : TermN n := .func f ![a]
def app2 {n : Nat} (f : Code 2) (a b : TermN n) : TermN n := .func f ![a,b]
def one {n : Nat} : TermN n := .func oneCode Fin.elim0
def state {n : Nat} (q : Nat) : TermN n := .func (constantCode q) ![.func (.zero 0) Fin.elim0]
def pack {n : Nat} (q l r : TermN n) : TermN n := app2 pairCode q (app2 pairCode l r)
def twice {n : Nat} (x : TermN n) : TermN n := app2 addCode x x

def zero {n : Nat} : TermN n := .func (Code.zero 0) Fin.elim0
def args (n : Nat) : Fin (n+2) → TermN (n+2) := Fin.snoc (fun i => .bvar i.succ) zero
def restCost (n : Nat) : TermN (n+2) := .func (costCode n) (fun i => args n i.succ)
def six {n : Nat} : TermN n := twice (app2 addCode (app2 addCode one one) one)
def outArgs (n : Nat) : Fin (n+2) → TermN (n+2) := Fin.cases six (fun i => args n i.succ)
def out (n : Nat) : TermN (n+2) := .func (returnCode n) (outArgs n)
def result (n : Nat) : TermN (n+2) := app2 block (app2 addCode #1 one) (out n)
def clock (n : Nat) : TermN (n+2) :=
    app2 addCode (app2 addCode (app2 addCode (app2 addCode
      (app2 addCode (app2 addCode one one) #1) (restCost n)) (state 6)) (restCost n))
      (app2 addCode (app2 addCode (app2 addCode #1 one) one) one)
def lhs (n : Nat) : TermN (n+2) := app2 PA194Stepper.stepper (clock n)
    (pack (state 2) #0 (.func (markedFile n) (args n)))
def rhs (n : Nat) : TermN (n+2) := pack (state 7) (app1 halfCode #0)
    (app2 addCode (app1 parityCode #0) (twice (result n)))
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

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valZero {n : Nat} (e : Fin n → M) : Semiterm.val e Empty.elim zero = (0 : M) := by
  simp only [zero,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

theorem modelSentence (n : Nat) : M↓[language] ⊧ sentence n := by
  apply (eqClosureModels _ _).mpr
  intro e
  let es : Fin (n+2) → M := fun i => Semiterm.val e Empty.elim (args n i)
  have hz : es (Fin.last (n+1)) = (0 : M) := by
    simp [es,args,valZero]
  have hfirst : es 0 = e 1 := by
    change Semiterm.val e Empty.elim (args n (Fin.castSucc 0)) = _
    simp [args,Semiterm.val_bvar]
  have h := modelFirstMarkedIncrement n es (e 0) hz
  let c3 : M := ((1 : M)+1)+1
  let sixM : M := c3+c3
  have hout : (fun i : Fin (n+2) => Semiterm.val e Empty.elim (outArgs n i)) =
      Fin.cases sixM (fun i => es i.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [outArgs,six,twice,valApp2,valOne]
      rfl
    · rfl
  simp only [lhs,rhs,clock,pack,twice,result,out,restCost,valApp2,valApp1,valState,valOne,
    Semiterm.val_bvar,Semiterm.val_func,Function.comp_def]
  rw [hout]
  rw [hfirst] at h
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
end PA194IncrementReturnSentence
