import PA194Site30Jump
import PA194StartupSentence
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194Site30JumpSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194StateOne PA194ZeroRuns PA194Path27Header PA194StartupSentence
abbrev T := TermN 2
def A (a b : T) : T := app2 addCode a b
def times2 (a : T) : T := app1 doubleCode a
def oneT : T := one
def succT (t : T) : T := A t oneT
def wordTerm : List Bool → T → T
  | [], t => t
  | b::bs, t => let x := times2 (wordTerm bs t); if b then A x oneT else x
def k : T := .bvar 0
def file : T := .bvar 1
def c (n : Nat) : T := state n
def base : T := A oneT (A file file)
def inputRight : T := wordTerm (PA194SourceProgram.path 30) (app2 zeros (succT (succT k)) base)
def outputRight : T := wordTerm (PA194SourceProgram.path 27) (app2 zeros (succT (succT (succT (succT k)))) base)
def lhs : T := app2 PA194Stepper.stepper (c 40) (PA194StartupSentence.pack (c 24) oneT inputRight)
def rhs : T := PA194StartupSentence.pack (c 24) oneT outputRight
def sentence : Sentence language := equalClosure lhs rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem valWord (e : Fin 2 → M) (xs : List Bool) (t : T) :
    Semiterm.val e Empty.elim (wordTerm xs t) = modelWord (M := M) xs (Semiterm.val e Empty.elim t) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [wordTerm, Bool.false_eq_true, ↓reduceIte, modelWord,
      A, times2, oneT, valApp1, valApp2, modelDoubleCode, valOne, ih]
    rfl

theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  apply (eqClosureModels _ _).mpr
  intro e
  have h := PA194Site30Jump.jumpPath30To27 (M := M) (e 0) (e 1)
  dsimp only at h
  simp only [lhs,rhs,c,inputRight,outputRight,PA194StartupSentence.pack,base,succT,A,
    oneT,valApp2,valState,valOne,valWord,k,file,Semiterm.val_bvar]
  exact h
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
end PA194Site30JumpSentence
