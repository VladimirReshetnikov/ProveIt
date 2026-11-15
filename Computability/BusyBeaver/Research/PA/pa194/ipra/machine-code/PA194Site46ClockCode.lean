import PA194Site46ClockExact
import PA194StartupSentence
import DiophantineConsistency.PRATermCompilation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site46ClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194FiniteControls PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194MarkedFile PA194StartupSentence
abbrev T := TermN 13
def A (a b : T) : T := app2 addCode a b
def oneT : T := one
def num (n : Nat) : T := state n
def succT (a : T) : T := A a oneT
def k : T := .bvar 0
def count : T := .bvar 1
def args : Fin 11 → T := fun i => .bvar ⟨i.val+2,by omega⟩
def v : Fin 11 → T := physicalArgs args
def selectedVec : Fin 7 → T := ![v 4,v 5,v 6,v 7,v 8,v 9,v 10]
def tailVec : Fin 6 → T := ![v 5,v 6,v 7,v 8,v 9,v 10]
def prefixVec : Fin 5 → T := ![v 0,v 1,v 2,v 3,.func (markedFile 5) selectedVec]
def costA : T := .func (PA194CarryFile.costCode 4) prefixVec
def costB : T := .func (PA194CarryFile.costCode 5) tailVec

def clockTerm : T :=
  let n := succT (succT k)
  let c := A (A (A (A (num 7) (num 1)) (num 1)) (succT n)) oneT
  let first := A (A c n) (num 23)
  let c01 := A (succT (succT (v 0))) (succT (succT (v 1)))
  let d23 := A (succT (succT (v 2))) (succT (succT (v 3)))
  let c14 := A (A (A (A first (num 8)) (succT n)) c01) d23
  let four := A (A (A (succT (v 3)) (succT (succT (v 2)))) (succT (succT (v 1)))) (succT (succT (v 0)))
  let front := A (A (A oneT oneT) (v 4)) costB
  let tri := A (A count count) count
  let t0 := num 23
  let t1 := A (A (A oneT k) (num 3)) t0
  let t2 := A (A (A (succT (num 2)) k) oneT) t1
  let t3 := A (num 2) t2
  let t4 := A n t3
  let t5 := A costA t4
  let t6 := A (succT (succT (succT (v 4)))) t5
  let t7 := A costB t6
  let t8 := A tri t7
  let t9 := A (num 2) t8
  let t10 := A (num 3) t9
  let t11 := A tri t10
  let t12 := A oneT t11
  let t13 := A front t12
  let t14 := A costA t13
  let t15 := A (succT k) t14
  let t16 := A (num 9) t15
  let t17 := A (num 24) t16
  let t18 := A (succT n) t17
  let t19 := A four t18
  let t20 := A (num 3) t19
  A c14 t20

def clockCode : Code 13 := compileTerm clockTerm
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem hv (e : Fin 13 → M) (i : Fin 11) : Semiterm.val e Empty.elim (v i) =
    physicalArgs (fun j : Fin 11 => e ⟨j.val+2,by omega⟩) i := by fin_cases i <;> rfl

theorem valSelected (e : Fin 13 → M) :
    (fun i : Fin 7 => Semiterm.val e Empty.elim (selectedVec i)) =
      PA194Site46MarkedFile.selectedArgs (fun j => e ⟨j.val+2,by omega⟩) := by
  funext i
  fin_cases i <;> exact hv e _

theorem valTail (e : Fin 13 → M) :
    (fun i : Fin 6 => Semiterm.val e Empty.elim (tailVec i)) =
      (fun i => PA194Site46MarkedFile.selectedArgs (fun j => e ⟨j.val+2,by omega⟩) i.succ) := by
  funext i
  fin_cases i <;> exact hv e _

theorem valPrefix (e : Fin 13 → M) :
    (fun i : Fin 5 => Semiterm.val e Empty.elim (prefixVec i)) =
      PA194Site46MarkedFile.prefixArgs (fun j => e ⟨j.val+2,by omega⟩) := by
  funext i
  fin_cases i
  · exact hv e 0
  · exact hv e 1
  · exact hv e 2
  · exact hv e 3
  · change Semiterm.val e Empty.elim (.func (markedFile 5) selectedVec) = _
    simp only [Semiterm.val_func,Function.comp_def,valSelected]
    rfl

theorem valA (e : Fin 13 → M) : Semiterm.val e Empty.elim costA =
    F (PA194CarryFile.costCode 4) (PA194Site46MarkedFile.prefixArgs (fun j => e ⟨j.val+2,by omega⟩)) := by
  simp only [costA,Semiterm.val_func,Function.comp_def,valPrefix]

theorem valB (e : Fin 13 → M) : Semiterm.val e Empty.elim costB =
    F (PA194CarryFile.costCode 5) (fun i => PA194Site46MarkedFile.selectedArgs (fun j => e ⟨j.val+2,by omega⟩) i.succ) := by
  simp only [costB,Semiterm.val_func,Function.comp_def,valTail]

theorem modelClock (e : Fin 13 → M) :
    F clockCode e = PA194Site46ClockExact.clock (e 0) (e 1) (fun i => e ⟨i.val+2,by omega⟩) := by
  rw [clockCode,modelCompile]
  simp only [clockTerm,A,oneT,num,succT,k,count,hv e 0,hv e 1,hv e 2,hv e 3,hv e 4,
    valA e,valB e,valApp2,valState,valOne,Semiterm.val_bvar]
  dsimp only [PA194Site46ClockExact.clock,PA194Site46SecondTo17.clock14,
    PA194Site46SecondTo95.firstClock,PA194Site46SecondTo17.fourCost]
  simp only [modelNumeralOne]
  rfl
#print axioms valSelected
#print axioms valTail
#print axioms valPrefix
#print axioms valA
#print axioms valB
#print axioms modelClock
end models
end PA194Site46ClockCode
