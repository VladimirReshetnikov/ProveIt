import PA194DecrementZeroFile
import PA194IncrementReturnSentence
set_option autoImplicit false
namespace PA194DecrementZeroFileSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194MarkedFile PA194CarryFile PA194ReturnFile PA194DecrementZeroFile PA194IncrementReturnSentence

def arity (p n : Nat) := p+n+3
def lterm (p n : Nat) : TermN (arity p n) := .bvar ⟨0,by simp [arity]⟩
def zero {p n : Nat} : TermN (arity p n) := .func (Code.zero 0) Fin.elim0
def restArgs (p n : Nat) : Fin (n+2) → TermN (arity p n) := fun i => .bvar ⟨p+1+i.val,by simp [arity]; omega⟩
def rest (p n : Nat) : TermN (arity p n) := .func (fileCode (n+1)) (restArgs p n)
def selected (p n : Nat) : TermN (arity p n) := app2 markedBlock zero (rest p n)
def prefixArgs (p n : Nat) : Fin (p+1) → TermN (arity p n) := Fin.snoc (fun i => .bvar ⟨i.val+1,by simp [arity]; omega⟩) (selected p n)
def output (p n : Nat) : TermN (arity p n) := .func (returnCode p) (Fin.cases (app2 PA194RegisterFile.block zero (rest p n)) (prefixArgs p n))
def cost (p n : Nat) : TermN (arity p n) := .func (costCode p) (prefixArgs p n)
def lhs (p n : Nat) : TermN (arity p n) := app2 PA194Stepper.stepper (app2 addCode (app2 addCode (cost p n) (state 7)) (cost p n))
  (PA194IncrementReturnSentence.pack (state 1) (lterm p n) (.func (fileCode p) (prefixArgs p n)))
def rhs (p n : Nat) : TermN (arity p n) := PA194IncrementReturnSentence.pack (state 11) (app1 halfCode (lterm p n))
  (app2 addCode (app1 parityCode (lterm p n)) (PA194IncrementReturnSentence.twice (output p n)))
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
  let er : Fin (n+2) → M := fun i => Semiterm.val e Empty.elim (restArgs p n i)
  let ep : Fin (p+1) → M := fun i => Semiterm.val e Empty.elim (prefixArgs p n i)
  let l := Semiterm.val e Empty.elim (lterm p n)
  have hz : Semiterm.val e Empty.elim (zero : TermN (arity p n)) = (0 : M) := by
    simp only [zero,Semiterm.val_func]
    congr 1
    exact Subsingleton.elim _ _
  have hp : ep (Fin.last p) = F markedBlock ![(0 : M),F (fileCode (n+1)) er] := by
    simp only [ep,prefixArgs,Fin.snoc_last,selected,valApp2,hz,rest,Semiterm.val_func,Function.comp_def]
    rfl
  have h := modelZeroDecrementFile p n ep er l hp
  have hout : (fun i : Fin (p+2) => Semiterm.val e Empty.elim (Fin.cases (app2 PA194RegisterFile.block zero (rest p n)) (prefixArgs p n) i)) =
      Fin.cases (F PA194RegisterFile.block ![(0 : M),F (fileCode (n+1)) er]) ep := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero,valApp2,hz,rest,Semiterm.val_func,Function.comp_def]
      rfl
    · rfl
  simp only [lhs,rhs,cost,output,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,
    valApp2,valApp1,valState,Semiterm.val_func,Function.comp_def,PA194StateOne.modelNumeralOne]
  rw [hout]
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  change F PA194Stepper.stepper ![(F (costCode p) ep+TableDispatch.modelNumeral M 7)+F (costCode p) ep,
    F pairCode ![(1 : M),F pairCode ![l,F (fileCode p) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(F (returnCode p) (Fin.cases (F PA194RegisterFile.block ![(0 : M),F (fileCode (n+1)) er]) ep)+F (returnCode p) (Fin.cases (F PA194RegisterFile.block ![(0 : M),F (fileCode (n+1)) er]) ep))]]
  simpa only [add_assoc] using h
end models
theorem classicalPRA (p n : Nat) : PRA ⊢ sentence p n := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence p n
theorem nativeIPRA (p n : Nat) : standardTheory ⊢ equalClosureI (lhs p n) (rhs p n) :=
  nativeOfClassical (lhs p n) (rhs p n) (classicalPRA p n)
#print axioms modelSentence
#print axioms nativeIPRA
end PA194DecrementZeroFileSentence
