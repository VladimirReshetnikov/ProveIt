import Mathlib.Tactic.FinCases
import PA194Path27To28
import PA194StartupSentence
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194Site27PositiveSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation
open PA194StartupSentence PA194Path27To28 PA194Path27Header PA194Path28Header PA194RegisterFile PA194UnaryRuns

abbrev T := TermN 12
def A (a b : T) : T := app2 addCode a b
def times2 (a : T) : T := app1 doubleCode a
def twiceIter : Nat → T → T
  | 0, t => t
  | n+1, t => times2 (twiceIter n t)
def args : Fin 11 → T := fun i => if i = 0 then app2 addCode (.bvar 1) one else .bvar i.succ
def updatedArgs : Fin 11 → T := Function.update args 0 (.bvar 1)
def k : T := .bvar 0
def v0 : T := args 2
def v1 : T := args 8
def v2 : T := args 1
def v3 : T := args 4
def v4 : T := args 3
def v5 : T := args 7
def v6 : T := args 0
def f : T := .func sourceFileCode args
def fupdated : T := .func sourceFileCode updatedArgs
def c (n : Nat) : T := state n
def oneT : T := one
def succT (t : T) : T := A t oneT
def ret : T := A (c 4) (succT (A (A (c 5) (c 6)) (c 2)))
def tail : T := .func (fileCode 3) ![args 5,args 6,args 9,args 10]
def selected : T := app2 ones v6 tail
def four (t : T) : T := times2 (times2 t)
def vec : Fin 7 → T := ![v0,v1,v2,v3,v4,v5,four selected]
def aa0 : T := A (A oneT oneT) oneT
def aa1 : T := A aa0 aa0
def aa2 : T := A aa1 aa1
def aa3 : T := A aa2 aa2
def aa4 : T := A (A aa3 aa3) oneT
def aa5 : T := A aa4 aa4
def aa6 : T := A aa5 aa5
def b : T := app2 ones (succT k) (A aa6 aa6)
def base : T := times2 (succT (times2 b))
def rev : Fin 6 → T := ![v4,v3,v2,v1,v0,base]
def ct (t : T) : T := succT (succT t)
def sixScan : T := A (A (A (A (A (ct v0) (ct v1)) (ct v2)) (ct v3)) (ct v4)) (ct v5)
def cr : T := A (A (c 2) (ct v5)) (.func (PA194CarryFile.costCode 5) rev)
def croot : T := A (A (succT (succT (succT k))) (A (c 3) (A (c 3) ret))) (c 0)
def ccarry : T := A (A (succT k) (.func (PA194CarryFile.costCode 6) vec)) (c 2)
def ctReturn (t : T) : T := A oneT (succT t)
def cret : T := A (A (A (A (A (ctReturn v5) (ctReturn v4)) (ctReturn v3)) (ctReturn v2)) (ctReturn v1)) (ctReturn v0)
def ch : T := A (A oneT (succT (succT k))) (c 3)
def cs : T := A (A (A (c 2) oneT) (succT k)) oneT
def cp : T := A (A (A oneT (succT k)) (c 3)) (A (c 2) (A (c 3) ret))
def firstClock : T := A (c 13) (A (succT (succT (succT (succT k)))) (succT (succT k)))
def clock : T :=
  let p0 := A firstClock (A (c 5) ret)
  let p1 := A p0 (c 8)
  let p2 := A p1 (succT (succT (succT k)))
  let p3 := A p2 (A sixScan cr)
  let p4 := A p3 (A (succT (succT (A oneT k))) (A (c 3) (A (c 3) ret)))
  let p5 := A p4 (c 13)
  let p6 := A p5 ccarry
  let p7 := A p6 (c 1)
  let p8 := A p7 cret
  let p9 := A p8 ch
  let p10 := A p9 cs
  A p10 cp
def wordTerm : List Bool → T → T
  | [], t => t
  | b::bs, t => let x := times2 (wordTerm bs t); if b then A x oneT else x
def inputRight : T := wordTerm (PA194SourceProgram.path 27)
  (app2 zeros (succT (succT k)) (A oneT (A f f)))
def outputRight : T := wordTerm (PA194SourceProgram.path 28)
  (app2 zeros (succT (succT k)) (A oneT (A fupdated fupdated)))
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
  have hm : es 0 = e 1 + (1 : M) := by
    change Semiterm.val e Empty.elim (app2 addCode (.bvar 1) one) = _
    rw [valApp2,valOne,Semiterm.val_bvar]
    rfl
  have hu : (fun i => Semiterm.val e Empty.elim (updatedArgs i)) = Function.update es 0 (e 1) := by
    funext i
    by_cases hi : i = 0
    · subst i; simp [updatedArgs,es,Semiterm.val_bvar]
    · simp [updatedArgs,es,Function.update_of_ne hi]
  have hRev : (fun i : Fin 6 => Semiterm.val e Empty.elim (rev i)) =
      ![es 3,es 4,es 1,es 8,es 2,Semiterm.val e Empty.elim base] := by
    funext i
    fin_cases i <;> rfl
  have hVec : (fun i : Fin 7 => Semiterm.val e Empty.elim (vec i)) =
      ![es 2,es 8,es 1,es 4,es 3,es 7,Semiterm.val e Empty.elim (four selected)] := by
    funext i
    fin_cases i <;> rfl
  have hTail : (fun i : Fin 4 => Semiterm.val e Empty.elim (![args 5,args 6,args 9,args 10] i)) =
      (fun i => es (inputOrder i.succ.succ.succ.succ.succ.succ.succ)) := by
    funext i
    fin_cases i <;> rfl
  have h := PA194Path27To28.positiveBranchPath27To28 (M := M) (e 0) (e 1) es hm
  dsimp only [Fin.cases_zero,Fin.cases_succ,physicalArgs,inputOrder] at h
  simp only [lhs,rhs,clock,firstClock,sixScan,cr,croot,ccarry,cret,ch,cs,cp,ct,ctReturn,ret,succT,A,
    aa0,aa1,aa2,aa3,aa4,aa5,aa6,
    v0,v1,v2,v3,v4,v5,v6,b,base,times2,
    inputRight,outputRight,PA194StartupSentence.pack,oneT,c,valApp2,valState,valOne,
    valWord,k,Semiterm.val_bvar,f,fupdated,Semiterm.val_func,Function.comp_def]
  rw [hu,hRev,hVec]
  simp only [base,selected,four,tail,b,aa0,aa1,aa2,aa3,aa4,aa5,aa6,
    v0,v1,v2,v3,v4,v5,v6,times2,succT,A,k,c,oneT,valApp2,valApp1,
    modelDoubleCode,valOne,valState,Semiterm.val_bvar,Semiterm.val_func,Function.comp_def]
  rw [hTail]
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
end PA194Site27PositiveSentence
