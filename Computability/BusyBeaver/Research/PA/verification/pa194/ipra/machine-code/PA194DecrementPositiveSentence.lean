import PA194DecrementPositive
import PA194IncrementReturnSentence
set_option autoImplicit false
namespace PA194DecrementPositiveSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194MarkedFile PA194CarryFile PA194ReturnFile PA194DecrementPositive PA194IncrementReturnSentence

def arity (p n : Nat) := p+n+3
def lterm (p n : Nat) : TermN (arity p n) := .bvar ⟨0,by simp [arity]⟩
def vterm (p n : Nat) : TermN (arity p n) := .bvar ⟨p+1,by simp [arity]; omega⟩
def restArgs (p n : Nat) : Fin (n+1) → TermN (arity p n) := fun i => .bvar ⟨p+2+i.val,by simp [arity]; omega⟩
def rest (p n : Nat) : TermN (arity p n) := .func (fileCode n) (restArgs p n)
def selected (p n : Nat) : TermN (arity p n) := app2 markedBlock (app2 addCode (vterm p n) one) (rest p n)
def prefixArgs (p n : Nat) : Fin (p+1) → TermN (arity p n) := Fin.snoc (fun i => .bvar ⟨i.val+1,by simp [arity]; omega⟩) (selected p n)
def output (p n : Nat) : TermN (arity p n) := .func (returnCode p) (Fin.cases (app2 PA194RegisterFile.block (vterm p n) (rest p n)) (prefixArgs p n))
def cost (p n : Nat) : TermN (arity p n) := .func (costCode p) (prefixArgs p n)
def lhs (p n : Nat) : TermN (arity p n) := app2 PA194Stepper.stepper (app2 addCode (app2 addCode (cost p n) (state 4)) (cost p n))
  (PA194IncrementReturnSentence.pack (state 1) (lterm p n) (.func (fileCode p) (prefixArgs p n)))
def rhs (p n : Nat) : TermN (arity p n) := PA194IncrementReturnSentence.pack (state 7) (lterm p n)
  (app2 addCode (PA194IncrementReturnSentence.twice (output p n)) one)
def sentence (p n : Nat) : Sentence language := equalClosure (lhs p n) (rhs p n)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence (p n : Nat) : M↓[language] ⊧ sentence p n := by
  apply (eqClosureModels _ _).mpr
  intro e
  let er : Fin (n+1) → M := fun i => Semiterm.val e Empty.elim (restArgs p n i)
  let ep : Fin (p+1) → M := fun i => Semiterm.val e Empty.elim (prefixArgs p n i)
  let v := Semiterm.val e Empty.elim (vterm p n)
  let l := Semiterm.val e Empty.elim (lterm p n)
  have hp : ep (Fin.last p) = F markedBlock ![v+1,F (fileCode n) er] := by
    simp only [ep,prefixArgs,Fin.snoc_last,selected,valApp2,valOne,rest,Semiterm.val_func,Function.comp_def]
    rfl
  have h := modelPositiveDecrement p n ep er v l hp
  have hout : (fun i : Fin (p+2) => Semiterm.val e Empty.elim (Fin.cases (app2 PA194RegisterFile.block (vterm p n) (rest p n)) (prefixArgs p n) i)) =
      Fin.cases (F PA194RegisterFile.block ![v,F (fileCode n) er]) ep := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero,valApp2,rest,Semiterm.val_func,Function.comp_def]
      rfl
    · rfl
  simp only [lhs,rhs,cost,output,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,
    valApp2,valState,valOne,Semiterm.val_func,Function.comp_def,PA194StateOne.modelNumeralOne]
  rw [hout]
  exact h
end models
theorem classicalPRA (p n : Nat) : PRA ⊢ sentence p n := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence p n
theorem nativeIPRA (p n : Nat) : standardTheory ⊢ equalClosureI (lhs p n) (rhs p n) :=
  nativeOfClassical (lhs p n) (rhs p n) (classicalPRA p n)
#print axioms modelSentence
#print axioms nativeIPRA
end PA194DecrementPositiveSentence
