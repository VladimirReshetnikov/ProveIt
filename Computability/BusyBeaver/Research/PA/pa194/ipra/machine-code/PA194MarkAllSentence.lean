import PA194MarkAll
import PA194MarkerPrefixSentence
set_option autoImplicit false
namespace PA194MarkAllSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PA194MarkAll PA194MarkerScan PA194MarkerPrefixSentence PA194RegisterFile PA194CarryFile PA194ReturnFile BinaryTapeCodes PA194IncrementReturnSentence

def outputArgs (n : Nat) : Fin (n+2) → TermN (n+2) := Fin.cases (PA194IncrementReturnSentence.twice (PA194IncrementReturnSentence.twice #1)) (PA194MarkerPrefixSentence.args n)
def lhs (i : Fin 8) : TermN (i.val+1+2) := app2 PA194Stepper.stepper
  (app2 addCode (app2 addCode (.func (costCode (i.val+1)) (PA194MarkerPrefixSentence.args (i.val+1))) (state 3)) (.func (costCode (i.val+1)) (PA194MarkerPrefixSentence.args (i.val+1))))
  (PA194IncrementReturnSentence.pack (state (markerControl i.succ)) #0 (.func (fileCode (i.val+1)) (PA194MarkerPrefixSentence.args (i.val+1))))
def rhs (i : Fin 8) : TermN (i.val+1+2) := PA194IncrementReturnSentence.pack (state 17) (app1 halfCode #0)
  (app2 addCode (app1 parityCode #0) (PA194IncrementReturnSentence.twice (.func (returnCode (i.val+1)) (outputArgs (i.val+1)))))
def sentence (i : Fin 8) : Sentence language := equalClosure (lhs i) (rhs i)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence (i : Fin 8) : M↓[language] ⊧ sentence i := by
  apply (eqClosureModels _ _).mpr
  intro e
  let ep : Fin (i.val+1+1) → M := fun j => Semiterm.val e Empty.elim (PA194MarkerPrefixSentence.args (i.val+1) j)
  have ht : ep (Fin.last (i.val+1)) = (e 1+e 1+1)+(e 1+e 1+1) := by
    simp [ep,PA194MarkerPrefixSentence.args,inputTail,PA194IncrementReturnSentence.twice,valApp2,valOne,Semiterm.val_bvar]
    rfl
  have bound : i.val+1 < 9 := by omega
  have h := modelMarkAllPositive i.val bound ep (e 0) (e 1) ht
  have ho : (fun j : Fin (i.val+1+2) => Semiterm.val e Empty.elim (outputArgs (i.val+1) j)) =
      Fin.cases ((e 1+e 1)+(e 1+e 1)) ep := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [outputArgs,PA194IncrementReturnSentence.twice,valApp2,Semiterm.val_bvar]
      rfl
    · rfl
  simp only [lhs,rhs,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,
    valApp2,valApp1,valState,Semiterm.val_bvar,Semiterm.val_func,Function.comp_def]
  rw [ho]
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  change F PA194Stepper.stepper ![(F (costCode (i.val+1)) ep + TableDispatch.modelNumeral M 3)+F (costCode (i.val+1)) ep,
    F pairCode ![TableDispatch.modelNumeral M (markerControl i.succ),F pairCode ![e 0,F (fileCode (i.val+1)) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 17,F pairCode ![F halfCode (fun _ => e 0),
      F parityCode (fun _ => e 0) + (F (returnCode (i.val+1)) (Fin.cases ((e 1+e 1)+(e 1+e 1)) ep) + F (returnCode (i.val+1)) (Fin.cases ((e 1+e 1)+(e 1+e 1)) ep))]]
  have hf : i.succ = (⟨i.val+1,bound⟩ : Fin 9) := by apply Fin.ext; rfl
  rw [hf]
  simpa only [add_assoc] using h
end models
theorem classicalPRA (i : Fin 8) : PRA ⊢ sentence i := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence i
theorem nativeIPRA (i : Fin 8) : standardTheory ⊢ equalClosureI (lhs i) (rhs i) :=
  nativeOfClassical (lhs i) (rhs i) (classicalPRA i)
#print axioms modelSentence
#print axioms nativeIPRA
end PA194MarkAllSentence
