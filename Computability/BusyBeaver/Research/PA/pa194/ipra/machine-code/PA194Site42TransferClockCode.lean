import PA194Site42PositiveClockCode
import PA194Site43ClockCode
import PA194SourceSite44Physical
import DiophantineConsistency.PRATermCompilation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site42TransferClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194FiniteControls PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194StartupSentence
abbrev T := TermN 14
def A (a b : T) : T := app2 addCode a b
def num (n : Nat) : T := state n
def k : T := .bvar 0
def count : T := .bvar 1
def m : T := .bvar 2
def args : Fin 11 → T := fun i => .bvar ⟨i.val+3,by omega⟩
def firstVec : Fin 12 → T := ![k,args 0,args 1,args 2,args 3,args 4,args 5,args 6,args 7,args 8,args 9,args 10]
def secondVec : Fin 13 → T := ![k,count,args 0,args 1,args 2,args 3,args 4,args 5,args 6,m,args 8,args 9,args 10]
def clockTerm : T := A (A (.func PA194Site42PositiveClockCode.clockCode firstVec)
  (.func PA194Site43ClockCode.clockCode secondVec)) (num 36)
def clockCode : Code 14 := compileTerm clockTerm
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

def inputArgs (e : Fin 14 → M) : Fin 11 → M := fun i => e ⟨i.val+3,by omega⟩
def firstInput (e : Fin 14 → M) : Fin 12 → M := Fin.cases (e 0) (inputArgs e)
def secondInput (e : Fin 14 → M) : Fin 13 → M :=
  Fin.cases (e 0) (Fin.cases (e 1) (Function.update (inputArgs e) 7 (e 2)))

theorem valFirst (e : Fin 14 → M) : (fun i : Fin 12 => Semiterm.val e Empty.elim (firstVec i)) = firstInput e := by
  funext i
  fin_cases i <;> rfl

theorem valSecond (e : Fin 14 → M) : (fun i : Fin 13 => Semiterm.val e Empty.elim (secondVec i)) = secondInput e := by
  funext i
  fin_cases i <;> rfl

theorem modelClock (e : Fin 14 → M) :
    F clockCode e =
      PA194Site42PositiveClockExact.clock (e 0) (inputArgs e) +
        PA194Site43ClockExact.clock (e 0) (e 1) (Function.update (inputArgs e) 7 (e 2)) + modelNumeral M 36 := by
  rw [clockCode,modelCompile]
  simp only [clockTerm,A,num,valApp2,valState,Semiterm.val_func,Function.comp_def,valFirst,valSecond,
    PA194Site42PositiveClockCode.modelClock,PA194Site43ClockCode.modelClock]
  rfl
#print axioms valFirst
#print axioms valSecond
#print axioms modelClock
end models
end PA194Site42TransferClockCode
