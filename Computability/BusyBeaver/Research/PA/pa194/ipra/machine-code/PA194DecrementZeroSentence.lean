import PA194DecrementZero
import PA194IncrementReturnSentence
set_option autoImplicit false
namespace PA194DecrementZeroSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open BinaryTapeCodes PA194RegisterFile PA194CarryFile PA194ReturnFile PA194DecrementZero PA194IncrementReturnSentence

def a {p : Nat} : TermN (p+2) := app2 addCode (PA194IncrementReturnSentence.twice #1) one
def b {p : Nat} : TermN (p+2) := PA194IncrementReturnSentence.twice a
def d {p : Nat} : TermN (p+2) := PA194IncrementReturnSentence.twice b
def f {p : Nat} : TermN (p+2) := PA194IncrementReturnSentence.twice d
def u {p : Nat} : TermN (p+2) := app2 addCode f (PA194IncrementReturnSentence.twice one)
def args (p : Nat) : Fin (p+1) → TermN (p+2) := Fin.snoc (fun i => .bvar i.succ.succ) f
def outArgs (p : Nat) : Fin (p+2) → TermN (p+2) := Fin.cases u (args p)
def cost (p : Nat) : TermN (p+2) := .func (costCode p) (args p)
def output (p : Nat) : TermN (p+2) := .func (returnCode p) (outArgs p)
def lhs (p : Nat) : TermN (p+2) := app2 PA194Stepper.stepper (app2 addCode (app2 addCode (cost p) (state 7)) (cost p))
  (PA194IncrementReturnSentence.pack (state 1) #0 (.func (fileCode p) (args p)))
def rhs (p : Nat) : TermN (p+2) := PA194IncrementReturnSentence.pack (state 11) (app1 halfCode #0)
  (app2 addCode (app1 parityCode #0) (PA194IncrementReturnSentence.twice (output p)))
def sentence (p : Nat) : Sentence language := equalClosure (lhs p) (rhs p)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence (p : Nat) : M↓[language] ⊧ sentence p := by
  apply (eqClosureModels _ _).mpr
  intro e
  let ep : Fin (p+1) → M := fun i => Semiterm.val e Empty.elim (args p i)
  have hp : ep (Fin.last p) = (((e 1+e 1+1)+(e 1+e 1+1))+((e 1+e 1+1)+(e 1+e 1+1)))+(((e 1+e 1+1)+(e 1+e 1+1))+((e 1+e 1+1)+(e 1+e 1+1))) := by
    simp [ep,args,f,d,b,a,PA194IncrementReturnSentence.twice,valApp2,valOne,Semiterm.val_bvar]
    rfl
  have h := modelZeroDecrement p ep (e 0) (e 1) hp
  let aM : M := e 1+e 1+1
  let bM : M := aM+aM
  let dM : M := bM+bM
  let fM : M := dM+dM
  let uM : M := fM+(1+1)
  have hout : (fun i : Fin (p+2) => Semiterm.val e Empty.elim (outArgs p i)) = Fin.cases uM ep := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [outArgs,u,f,d,b,a,PA194IncrementReturnSentence.twice,valApp2,valOne,Semiterm.val_bvar]
      rfl
    · rfl
  simp only [lhs,rhs,cost,output,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,
    valApp2,valApp1,valState,valOne,Semiterm.val_bvar,Semiterm.val_func,Function.comp_def,PA194StateOne.modelNumeralOne]
  rw [hout]
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  change F PA194Stepper.stepper ![(F (costCode p) ep+TableDispatch.modelNumeral M 7)+F (costCode p) ep,
    F pairCode ![(1 : M),F pairCode ![e 0,F (fileCode p) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => e 0),
      F parityCode (fun _ => e 0)+(F (returnCode p) (Fin.cases uM ep)+F (returnCode p) (Fin.cases uM ep))]]
  dsimp only [uM,fM,dM,bM,aM]
  simpa only [add_assoc] using h
end models
theorem classicalPRA (p : Nat) : PRA ⊢ sentence p := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence p
theorem nativeIPRA (p : Nat) : standardTheory ⊢ equalClosureI (lhs p) (rhs p) :=
  nativeOfClassical (lhs p) (rhs p) (classicalPRA p)
#print axioms modelSentence
#print axioms nativeIPRA
end PA194DecrementZeroSentence
