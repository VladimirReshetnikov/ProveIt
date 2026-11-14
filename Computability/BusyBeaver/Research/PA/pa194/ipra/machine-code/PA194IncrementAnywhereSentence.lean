import PA194IncrementAnywhere
import PA194IncrementReturnSentence
set_option autoImplicit false
namespace PA194IncrementAnywhereSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194RegisterFile PA194IncrementReturn PA194IncrementAnywhere PA194MarkedFile PA194CarryFile PA194ReturnFile PA194UnaryRuns BinaryTapeCodes TableDispatch PA194IncrementReturnSentence

def arity (p n : Nat) := p+n+2
def markedArgs (p n : Nat) : Fin (n+2) → TermN (arity p n) :=
  Fin.snoc (fun i => .bvar ⟨p+1+i.val,by simp [arity] <;> omega⟩) zero
def selected (p n : Nat) : TermN (arity p n) := .bvar ⟨p+1,by simp [arity] <;> omega⟩
def marked (p n : Nat) : TermN (arity p n) := .func (markedFile n) (markedArgs p n)
def prefixArgs (p n : Nat) : Fin (p+1) → TermN (arity p n) :=
  Fin.snoc (fun i => .bvar ⟨i.val+1,by simp [arity] <;> omega⟩) (marked p n)
def prefixCost (p n : Nat) : TermN (arity p n) := .func (costCode p) (prefixArgs p n)
def restCost (p n : Nat) : TermN (arity p n) := .func (costCode n) (fun i => markedArgs p n i.succ)
def outArgs (p n : Nat) : Fin (n+2) → TermN (arity p n) := Fin.cases six (fun i => markedArgs p n i.succ)
def result (p n : Nat) : TermN (arity p n) := app2 block (app2 addCode (selected p n) one) (.func (returnCode n) (outArgs p n))
def resultArgs (p n : Nat) : Fin (p+2) → TermN (arity p n) := Fin.cases (result p n) (prefixArgs p n)
def total (p n : Nat) : TermN (arity p n) :=
  app2 addCode (app2 addCode (prefixCost p n)
    (app2 addCode (app2 addCode (app2 addCode (app2 addCode (app2 addCode (app2 addCode one one) (selected p n)) (restCost p n)) (state 6)) (restCost p n))
      (app2 addCode (app2 addCode (app2 addCode (selected p n) one) one) one))) (prefixCost p n)
def lhs (p n : Nat) : TermN (arity p n) := app2 PA194Stepper.stepper (total p n)
    (PA194IncrementReturnSentence.pack (state 2) (.bvar ⟨0,by simp [arity]⟩) (.func (fileCode p) (prefixArgs p n)))
def rhs (p n : Nat) : TermN (arity p n) := PA194IncrementReturnSentence.pack (state 7) (app1 halfCode (.bvar ⟨0,by simp [arity]⟩))
    (app2 addCode (app1 parityCode (.bvar ⟨0,by simp [arity]⟩)) (PA194IncrementReturnSentence.twice (.func (returnCode p) (resultArgs p n))))
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
  let es : Fin (n+2) → M := fun i => Semiterm.val e Empty.elim (markedArgs p n i)
  let ep : Fin (p+1) → M := fun i => Semiterm.val e Empty.elim (prefixArgs p n i)
  have hz : es (Fin.last (n+1)) = (0 : M) := by simp [es,markedArgs,valZero]
  have hm : ep (Fin.last p) = F (markedFile n) es := by simp [ep,prefixArgs,marked,Semiterm.val_func,Function.comp_def,es]
  have hselected : Semiterm.val e Empty.elim (selected p n) = es 0 := by
    change Semiterm.val e Empty.elim (selected p n) = Semiterm.val e Empty.elim (markedArgs p n (Fin.castSucc 0))
    simp [selected,markedArgs]
  have h := modelIncrementAnywhereRaw p n ep es (e ⟨0,by simp [arity]⟩) hm hz
  let c3 : M := ((1 : M)+1)+1
  let sixM : M := c3+c3
  have hout : (fun i : Fin (n+2) => Semiterm.val e Empty.elim (outArgs p n i)) = Fin.cases sixM (fun i => es i.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [outArgs,six,PA194IncrementReturnSentence.twice,valApp2,valOne]
      rfl
    · rfl
  have hresult : Semiterm.val e Empty.elim (result p n) =
      F block ![es 0+1,F (returnCode n) (Fin.cases sixM (fun i => es i.succ))] := by
    simp only [result,valApp2,valOne,Semiterm.val_func,Function.comp_def,hselected,hout]
    rfl
  have hresultArgs : (fun i : Fin (p+2) => Semiterm.val e Empty.elim (resultArgs p n i)) =
      Fin.cases (F block ![es 0+1,F (returnCode n) (Fin.cases sixM (fun i => es i.succ))]) ep := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hresult
    · rfl
  simp only [lhs,rhs,total,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,result,restCost,prefixCost,valApp2,valApp1,valState,valOne,
    Semiterm.val_bvar,Semiterm.val_func,Function.comp_def]
  rw [hresultArgs,hselected]
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
end PA194IncrementAnywhereSentence
