import PA194Path25To26
import PA194StartupSentence
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194PositiveBranchSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation
open PA194StartupSentence PA194Path25To26 PA194Path27Header PA194Path27Frame PA194Path26Header

abbrev T := TermN 12
def A (a b : T) : T := app2 addCode a b
def times2 (a : T) : T := app1 doubleCode a
def twiceIter : Nat → T → T
  | 0, t => t
  | n+1, t => times2 (twiceIter n t)
def args : Fin 11 → T := fun i => if i = 8 then app2 addCode (.bvar 9) one else .bvar i.succ
def updatedArgs : Fin 11 → T := Function.update args 8 (.bvar 9)
def k : T := .bvar 0
def x : T := args 2
def f : T := .func sourceFileCode args
def fupdated : T := .func sourceFileCode updatedArgs
def c (n : Nat) : T := state n
def oneT : T := one
def succT (t : T) : T := A t oneT
def ret : T := A (c 4) (succT (A (A (c 5) (c 6)) (c 2)))
def scan : T := A (succT (succT (succT k))) (succT (succT x))
def back : T := A (succT x) (succT (succT (succT k)))
def c0 : T := A (A (c 12) (A (succT (succT (succT (succT k)))) (succT (succT k)))) (c 4)
def c1 : T := ret
def c2 : T := A (A (A (c 7) (A (A scan (c 3)) back)) (c 5)) ret
def c3 : T := A (A oneT (succT k)) (c 3)
def clock : T :=
  let p0 := A c0 c1
  let p1 := A p0 c2
  let p2 := A p1 (c 12)
  let p3 := A p2 k
  let p4 := A p3 (A (A (c 3) x) (c 2))
  let p5 := A p4 (c 1)
  let p6 := A p5 (c 1)
  let p7 := A p6 (succT x)
  let p8 := A p7 (A (A (c 2) k) (c 4))
  let p9 := A p8 (A (A (A (c 2) oneT) (succT k)) oneT)
  A p9 (A c3 (A (c 4) ret))
def wordTerm : List Bool → T → T
  | [], t => t
  | b::bs, t => let x := times2 (wordTerm bs t); if b then A x oneT else x
def inputRight : T := wordTerm (PA194SourceProgram.path 25)
  (app2 zeros (succT (succT k)) (A oneT (A f f)))
def outputRight : T := wordTerm (PA194SourceProgram.path 26)
  (app2 zeros (succT (succT (succT k))) (A oneT (A fupdated fupdated)))
def lhs : T := app2 PA194Stepper.stepper clock (PA194StartupSentence.pack (c 24) oneT inputRight)
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

theorem valWord (e : Fin 12 → M) (xs : List Bool) (t : T) :
    Semiterm.val e Empty.elim (wordTerm xs t) =
      modelWord (M := M) xs (Semiterm.val e Empty.elim t) := by
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
  let es : Fin 11 → M := fun i => Semiterm.val e Empty.elim (args i)
  have hm : es 8 = e 9 + (1 : M) := by
    change Semiterm.val e Empty.elim (app2 addCode (.bvar 9) one) = _
    rw [valApp2,valOne,Semiterm.val_bvar]
    rfl
  have hu : (fun i => Semiterm.val e Empty.elim (updatedArgs i)) = Function.update es 8 (e 9) := by
    funext i
    by_cases hi : i = 8
    · subst i; simp [updatedArgs,es,Semiterm.val_bvar]
    · simp [updatedArgs,es,Function.update_of_ne hi]
  have h := PA194Path25To26.positiveBranchPath25To26 (M := M) (e 0) (e 9) es hm
  dsimp only [Fin.cases_zero,Fin.cases_succ,physicalArgs,inputOrder] at h
  simp only [lhs,rhs,clock,c0,c1,c2,c3,scan,back,ret,succT,A,
    inputRight,outputRight,PA194StartupSentence.pack,oneT,c,valApp2,valState,valOne,
    valWord,k,x,Semiterm.val_bvar,f,fupdated,Semiterm.val_func,Function.comp_def]
  rw [hu]
  convert h using 1 <;> rfl

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
end PA194PositiveBranchSentence
