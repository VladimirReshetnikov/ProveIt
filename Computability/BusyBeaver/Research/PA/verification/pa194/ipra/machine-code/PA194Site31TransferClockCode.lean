import PA194SourceSite31CodedLoop
import DiophantineConsistency.PRATermCompilation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace PA194Site31TransferClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PA194StartupSentence PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194FiniteControls TableDispatch
abbrev T := TermN 14
def A (a b : T) : T := app2 addCode a b
def x (i : Fin 13) : T := .bvar ⟨i.val,by have h := i.isLt; omega⟩
def gap : T := .bvar 13
def first : Fin 11 → T := ![A (x 0) one,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 12,
  app2 PA194OneSpareReturn.repeatOutput (.func Code.succ ![x 11]) (state 0)]
def total : T := A (A (.func PA194Site31CodedClock.clockCode x)
  (.func PA194Site32PositiveClockCode.clockCode (Fin.cons gap first))) (state 34)
def clockCode : Code 14 := compileTerm total
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun a b => F addCode ![a,b]⟩
local instance : Mul M := ⟨fun a b => F mulCode ![a,b]⟩
local instance : LT M := ⟨fun a b => Structure.rel (L := language) Language.ORing.Rel.lt ![a,b]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

def env13 (e : Fin 14 → M) : Fin 13 → M := fun i => e ⟨i.val,by have h := i.isLt; omega⟩

theorem valX (e : Fin 14 → M) :
    (fun i => Semiterm.val e Empty.elim (x i)) = env13 e := by
  funext i; rfl

theorem valFirst (e : Fin 14 → M) :
    (fun i => Semiterm.val e Empty.elim (first i)) =
      PA194Site31OutputFile.updated (PA194Site31SentenceClock.args (env13 e)) (env13 e 11) := by
  funext i
  fin_cases i <;>
    simp [first,A,x,PA194Site31OutputFile.updated,PA194Site31SentenceClock.args,
      PA194Site31SentenceClock.regs,PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args,
      valApp2,valState,valOne,Semiterm.val_func,Semiterm.val_bvar,Function.comp_def,env13] <;> rfl

theorem modelClock (e : Fin 14 → M) :
    F clockCode e = F addCode ![F addCode ![F PA194Site31CodedClock.clockCode (env13 e),
      F PA194Site32PositiveClockCode.clockCode (Fin.cons (e 13)
        (PA194Site31OutputFile.updated (PA194Site31SentenceClock.args (env13 e)) (env13 e 11)))],
      modelNumeral M 34] := by
  have ha : (fun i : Fin 12 => Semiterm.val e Empty.elim ((Fin.cons gap first : Fin 12 → T) i)) =
      Fin.cons (e 13) (PA194Site31OutputFile.updated (PA194Site31SentenceClock.args (env13 e)) (env13 e 11)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (valFirst e) j
  rw [clockCode,modelCompile]
  simp only [total,A,valApp2,Semiterm.val_func,Function.comp_def,valX,valState,ha]
#print axioms valFirst
#print axioms modelClock
end models
end PA194Site31TransferClockCode
