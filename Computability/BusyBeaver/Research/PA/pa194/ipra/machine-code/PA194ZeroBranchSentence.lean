import PA194Site27Step
import PA194StartupSentence
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194ZeroBranchSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation
open PA194StartupSentence PA194Site27Step

abbrev T := TermN 12
def A (a b : T) : T := app2 addCode a b
def times2 (a : T) : T := app1 doubleCode a
def twiceIter : Nat → T → T
  | 0, t => t
  | n+1, t => times2 (twiceIter n t)
def args : Fin 11 → T := fun i => if i = 8 then zero else .bvar i.succ
def k : T := .bvar 0
def x : T := args 2
def f : T := .func sourceFileCode args
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
  let p6 := A p5 (A (A (c 2) (c 2)) x)
  let p7 := A p6 (A (A (c 2) (succT k)) (c 4))
  let p8 := A p7 (A (A (A (c 2) oneT) (succT k)) oneT)
  A p8 (A c3 (A (c 3) ret))
def inputRight : T := A (twiceIter 8 (app2 zeros k (succT (A f f)))) oneT
def outputRight : T := A (A (twiceIter 7 (app2 zeros (succT k) (succT (A f f)))) (twiceIter 4 oneT)) oneT
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

theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  apply (eqClosureModels _ _).mpr
  intro e
  let es : Fin 11 → M := fun i => Semiterm.val e Empty.elim (args i)
  have hz : es 8 = (0 : M) := by simp [es,args,valZero]
  have h := PA194Site27Step.zeroBranchSite27 (M := M) (e 0) es hz
  dsimp only [Fin.cases_zero,Fin.cases_succ,physicalArgs,inputOrder] at h
  simp only [lhs,rhs,clock,c0,c1,c2,c3,scan,back,ret,succT,A,
    inputRight,outputRight,PA194StartupSentence.pack,oneT,c,valApp2,valState,valOne,
    twiceIter,times2,valApp1,modelDoubleCode,k,x,Semiterm.val_bvar,
    f,Semiterm.val_func,Function.comp_def] 
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
end PA194ZeroBranchSentence
