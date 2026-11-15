import PA194Site45ZeroClockExact
import PA194Site32ClockValuations
import DiophantineConsistency.PRATermCompilation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site45ZeroClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194FiniteControls PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194MarkedFile PA194StartupSentence PA194Site32PositiveClockCode
abbrev T := TermN 12

def tailTerm : T := app2 ones (succT (v 9)) (v 10)
def qTerm45 : T := app2 ones zero (twice tailTerm)
def nineTerm : Fin 10 → T := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,zero,twice (twice qTerm45)]
def rollbackTerm : T := A (A (num 1) (num 2)) (.func (PA194CarryFile.costCode 9) nineTerm)

def clockTerm : T :=
  let n := succT (succT k)
  let c := A (A (A (num 7) (num 1)) (succT n)) oneT
  let first := A (A c n) (num 22)
  let c01 := A (succT (succT (v 0))) (succT (succT (v 1)))
  let scan := A (A (A (A (A (succT (succT (v 2))) (succT (succT (v 3)))) (succT (succT (v 4)))) (succT (succT (v 5)))) (succT (succT (v 6)))) (succT (succT (v 7)))
  let c14 := A (A (A (A first (num 7)) (succT n)) c01) scan
  let six := A (A (A (A (A (succT (v 7)) (succT (succT (v 6)))) (succT (succT (v 5)))) (succT (succT (v 4)))) (succT (succT (v 3)))) (succT (succT (v 2)))
  let c12 := A (A rollbackTerm (succT k)) (num 6)
  let c14z := succT (A (succT (num 4)) (succT k))
  let c16z := A (A oneT (succT (succT (succT k)))) (num 3)
  let zclock := A (A c12 c14z) c16z
  A c14 (A (num 3) (A six (A (succT (succT (v 1))) (A (succT (succT (v 0))) (A (succT n) (A (num 23) (A (num 8) (A carryTerm (A zclock (num 19))))))))))

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

theorem carryValue (e : Fin 12 → M) :
    Semiterm.val e Empty.elim carryTerm =
      ((e 0+1)+F (PA194CarryFile.costCode 8) (PA194Site45MarkedFile.prefixArgs (fun j => e j.succ)))+modelNumeral M 2 := by
  rw [valCarry]
  congr 2
  let v' := physicalArgs (fun j : Fin 11 => e j.succ)
  have hmarked : F (markedFile 1) (PA194Site45MarkedFile.selectedArgs (fun j => e j.succ)) =
      (modelQ e+modelQ e)+(modelQ e+modelQ e) := by
    rw [modelMarkedFile,modelMarkedBlock]
    have ht : (fun i : Fin 2 => PA194Site45MarkedFile.selectedArgs (fun j => e j.succ) i.succ) = ![v' 9,v' 10] := by
      funext i
      fin_cases i <;> rfl
    rw [ht]
    rfl
  dsimp only [PA194Site45MarkedFile.prefixArgs]
  rw [hmarked]

theorem valNine (e : Fin 12 → M) :
    (fun i : Fin 10 => Semiterm.val e Empty.elim (nineTerm i)) =
      PA194Site32ZeroFile.nine (fun j => e j.succ) := by
  funext i
  fin_cases i <;> simp [nineTerm,qTerm45,tailTerm,PA194Site32PositiveClockCode.twice,A,succT,oneT,valApp2,valZero,valOne,hv e,
    PA194Site32ZeroFile.nine,PA194Site32ZeroFile.tailWord,physicalArgs,inputOrder] <;> rfl

theorem valRollback (e : Fin 12 → M) :
    Semiterm.val e Empty.elim rollbackTerm = PA194Site45ZeroRollback.cost (fun j => e j.succ) := by
  simp only [rollbackTerm,A,num,valApp2,valState,Semiterm.val_func,Function.comp_def,valNine]
  rfl

theorem modelClock (e : Fin 12 → M) :
    F clockCode e = PA194Site45ZeroClockExact.clock (e 0) (fun i => e i.succ) := by
  rw [clockCode,modelCompile]
  simp only [clockTerm,A,oneT,num,succT,k,hv e 0,hv e 1,hv e 2,hv e 3,hv e 4,hv e 5,hv e 6,hv e 7,
    carryValue e,valRollback e,valApp2,valState,valOne,Semiterm.val_bvar]
  dsimp only [PA194Site45ZeroClockExact.clock,PA194Site45SecondTo14.clock,
    PA194Site45SecondTo14.scanCost,PA194Site45SecondTo60.firstClock,PA194Site45SecondTo17.sixCost,
    PA194Site45ZeroTo16.clock]
  simp only [modelNumeralOne]
  rfl
#print axioms carryValue
#print axioms valNine
#print axioms valRollback
#print axioms modelClock
end models
end PA194Site45ZeroClockCode
