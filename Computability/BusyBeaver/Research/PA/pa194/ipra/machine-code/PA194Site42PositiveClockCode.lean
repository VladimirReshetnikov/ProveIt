import PA194Site42PositiveClockExact
import PA194StartupSentence
import DiophantineConsistency.PRATermCompilation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site42PositiveClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194FiniteControls PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194MarkedFile PA194StartupSentence
abbrev T := TermN 12
def A (a b : T) : T := app2 addCode a b
def oneT : T := one
def num (n : Nat) : T := state n
def succT (a : T) : T := A a oneT
def k : T := .bvar 0
def args : Fin 11 → T := fun i => .bvar i.succ
def v : Fin 11 → T := physicalArgs args
def selectedVec : Fin 6 → T := ![v 5,v 6,v 7,v 8,v 9,v 10]
def tailVec : Fin 5 → T := ![v 6,v 7,v 8,v 9,v 10]
def prefixVec : Fin 6 → T := ![v 0,v 1,v 2,v 3,v 4,.func (markedFile 4) selectedVec]
def costA : T := .func (PA194CarryFile.costCode 5) prefixVec

def clockTerm : T :=
  let n := succT (succT k)
  let c := A (A (A (A (num 7) (num 3)) oneT) (succT n)) oneT
  let first := A (A c n) (num 23)
  let scan := A (A (A (A (succT (succT (v 0))) (succT (succT (v 1)))) (succT (succT (v 2)))) (succT (succT (v 3)))) (succT (succT (v 4)))
  let c14 := A (A (A first (num 10)) (succT n)) scan
  let ret := A oneT (A (A (A (A (A oneT (succT (v 4))) (A oneT (succT (v 3)))) (A oneT (succT (v 2)))) (A oneT (succT (v 1)))) (A oneT (succT (v 0))))
  let h12 := A (A oneT n) (num 3)
  let h14 := succT (A (succT (num 2)) (succT k))
  let h16 := A (A oneT (succT k)) (num 3)
  let positive := A (A (A ret h12) h14) h16
  let carry := A (A (succT k) costA) (num 2)
  A c14 (A (num 3) (A (A (succT (v 4)) (succT (succT (v 3)))) (A (succT (succT (v 2))) (A (succT (succT (v 1))) (A (succT (succT (v 0))) (A (succT n) (A (num 24) (A (num 11) (A carry (A positive (num 23)))))))))))

def clockCode : Code 12 := compileTerm clockTerm
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem hv (e : Fin 12 → M) (i : Fin 11) : Semiterm.val e Empty.elim (v i) =
    physicalArgs (fun j : Fin 11 => e j.succ) i := by fin_cases i <;> rfl

theorem valSelected (e : Fin 12 → M) :
    (fun i : Fin 6 => Semiterm.val e Empty.elim (selectedVec i)) =
      PA194Site42MarkedFile.selectedArgs (fun j => e j.succ) := by
  funext i
  fin_cases i <;> exact hv e _

theorem valTail (e : Fin 12 → M) :
    (fun i : Fin 5 => Semiterm.val e Empty.elim (tailVec i)) =
      (fun i => PA194Site42MarkedFile.selectedArgs (fun j => e j.succ) i.succ) := by
  funext i
  fin_cases i <;> exact hv e _

theorem valPrefix (e : Fin 12 → M) :
    (fun i : Fin 6 => Semiterm.val e Empty.elim (prefixVec i)) =
      PA194Site42MarkedFile.prefixArgs (fun j => e j.succ) := by
  funext i
  fin_cases i
  · exact hv e 0
  · exact hv e 1
  · exact hv e 2
  · exact hv e 3
  · exact hv e 4
  · change Semiterm.val e Empty.elim (.func (markedFile 4) selectedVec) = _
    simp only [Semiterm.val_func,Function.comp_def,valSelected]
    rfl

theorem valA (e : Fin 12 → M) : Semiterm.val e Empty.elim costA =
    F (PA194CarryFile.costCode 5) (PA194Site42MarkedFile.prefixArgs (fun j => e j.succ)) := by
  simp only [costA,Semiterm.val_func,Function.comp_def,valPrefix]

theorem modelClock (e : Fin 12 → M) :
    F clockCode e = PA194Site42PositiveClockExact.clock (e 0) (fun i => e i.succ) := by
  rw [clockCode,modelCompile]
  simp only [clockTerm,A,oneT,num,succT,k,hv e 0,hv e 1,hv e 2,hv e 3,hv e 4,
    valA e,valApp2,valState,valOne,Semiterm.val_bvar]
  dsimp only [PA194Site42PositiveClockExact.clock,PA194Site42SecondTo14.clock,PA194Site42SecondTo14.scanCost,PA194Site42SecondTo71.firstClock,
    PA194Site42PositiveTo16.clock,PA194Site38PositiveReturnExact.returnCost]
  simp only [modelNumeralOne]
  rfl
#print axioms valSelected
#print axioms valTail
#print axioms valPrefix
#print axioms valA
#print axioms modelClock
end models
end PA194Site42PositiveClockCode
