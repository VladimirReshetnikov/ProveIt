import PA194MarkerPrefix
import PA194IncrementReturnSentence
set_option autoImplicit false
namespace PA194MarkerPrefixSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194MarkerScan PA194MarkerPrefix PA194RegisterFile PA194CarryFile BinaryTapeCodes PA194IncrementReturnSentence

def inputTail {n : Nat} : TermN (n+2) := PA194IncrementReturnSentence.twice (app2 addCode (PA194IncrementReturnSentence.twice #1) one)
def args (n : Nat) : Fin (n+1) → TermN (n+2) := Fin.snoc (fun i => .bvar i.succ.succ) inputTail
def leftArgs (n : Nat) : Fin (n+2) → TermN (n+2) := Fin.cases #0 (args n)
def leftTape (n : Nat) : TermN (n+2) := .func (PA194PrefixFile.leftCode n) (leftArgs n)
def lhs (i : Fin 9) : TermN (i.val+2) := app2 PA194Stepper.stepper
  (app2 addCode (.func (costCode i.val) (args i.val)) (state 3))
  (PA194IncrementReturnSentence.pack (state (markerControl i)) #0 (.func (fileCode i.val) (args i.val)))
def rhs (i : Fin 9) : TermN (i.val+2) := PA194IncrementReturnSentence.pack (state 15) (app1 halfCode (leftTape i.val))
  (app2 addCode (app1 parityCode (leftTape i.val)) (PA194IncrementReturnSentence.twice (PA194IncrementReturnSentence.twice (PA194IncrementReturnSentence.twice #1))))
def sentence (i : Fin 9) : Sentence language := equalClosure (lhs i) (rhs i)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence (i : Fin 9) : M↓[language] ⊧ sentence i := by
  apply (eqClosureModels _ _).mpr
  intro e
  let ep : Fin (i.val+1) → M := fun j => Semiterm.val e Empty.elim (args i.val j)
  have ht : ep (Fin.last i.val) = (e 1+e 1+1)+(e 1+e 1+1) := by
    simp [ep,args,inputTail,PA194IncrementReturnSentence.twice,valApp2,valOne,Semiterm.val_bvar]
    rfl
  have h := modelMarkerPrefixAndDelimiter i.val i.isLt ep (e 0) (e 1) ht
  have hl : (fun j : Fin (i.val+2) => Semiterm.val e Empty.elim (leftArgs i.val j)) = Fin.cases (e 0) ep := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [leftArgs,Semiterm.val_bvar]
    · rfl
  simp only [lhs,rhs,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,leftTape,
    valApp2,valApp1,valState,Semiterm.val_bvar,Semiterm.val_func,Function.comp_def]
  rw [hl]
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  change F PA194Stepper.stepper ![F (costCode i.val) ep + TableDispatch.modelNumeral M 3,
    F pairCode ![TableDispatch.modelNumeral M (markerControl i),F pairCode ![e 0,F (fileCode i.val) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 15,F pairCode ![F halfCode (fun _ => F (PA194PrefixFile.leftCode i.val) (Fin.cases (e 0) ep)),
      F parityCode (fun _ => F (PA194PrefixFile.leftCode i.val) (Fin.cases (e 0) ep)) + (((e 1+e 1)+(e 1+e 1))+((e 1+e 1)+(e 1+e 1)))]]
  simpa only [add_assoc] using h
end models
theorem classicalPRA (i : Fin 9) : PRA ⊢ sentence i := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence i
theorem nativeIPRA (i : Fin 9) : standardTheory ⊢ equalClosureI (lhs i) (rhs i) :=
  nativeOfClassical (lhs i) (rhs i) (classicalPRA i)
#print axioms modelSentence
#print axioms nativeIPRA
end PA194MarkerPrefixSentence
