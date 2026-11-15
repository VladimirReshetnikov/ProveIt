import PA194Site45PositiveClockExact
import PA194Site32ClockValuations
import DiophantineConsistency.PRATermCompilation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site45PositiveClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194FiniteControls PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194MarkedFile PA194StartupSentence PA194Site32PositiveClockCode
abbrev T := TermN 12

def clockTerm : T :=
  let n := succT (succT k)
  let c := A (A (A (num 7) (num 1)) (succT n)) oneT
  let first := A (A c n) (num 22)
  let c01 := A (succT (succT (v 0))) (succT (succT (v 1)))
  let scan := A (A (A (A (A (succT (succT (v 2))) (succT (succT (v 3)))) (succT (succT (v 4)))) (succT (succT (v 5)))) (succT (succT (v 6)))) (succT (succT (v 7)))
  let c14 := A (A (A (A first (num 7)) (succT n)) c01) scan
  let six := A (A (A (A (A (succT (v 7)) (succT (succT (v 6)))) (succT (succT (v 5)))) (succT (succT (v 4)))) (succT (succT (v 3)))) (succT (succT (v 2)))
  let ret := A oneT (A (A (A (A (A (A (A (A oneT (succT (v 7))) (A oneT (succT (v 6)))) (A oneT (succT (v 5)))) (A oneT (succT (v 4)))) (A oneT (succT (v 3)))) (A oneT (succT (v 2)))) (A oneT (succT (v 1)))) (A oneT (succT (v 0))))
  let h12 := A (A oneT n) (num 3)
  let h14 := succT (A (succT (num 2)) (succT k))
  let h16 := A (A oneT (succT k)) (num 3)
  let positive := A (A (A ret h12) h14) h16
  A c14 (A (num 3) (A six (A (succT (succT (v 1))) (A (succT (succT (v 0))) (A (succT n) (A (num 23) (A (num 8) (A carryTerm (A positive (num 22))))))))))

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

theorem modelClock (e : Fin 12 → M) :
    F clockCode e = PA194Site45PositiveClockExact.clock (e 0) (fun i => e i.succ) := by
  rw [clockCode,modelCompile]
  simp only [clockTerm,A,oneT,num,succT,k,hv e 0,hv e 1,hv e 2,hv e 3,hv e 4,hv e 5,hv e 6,hv e 7,
    carryValue e,valApp2,valState,valOne,Semiterm.val_bvar]
  dsimp only [PA194Site45PositiveClockExact.clock,PA194Site45SecondTo14.clock,
    PA194Site45SecondTo14.scanCost,PA194Site45SecondTo60.firstClock,PA194Site45SecondTo17.sixCost,
    PA194Site45PositiveTo16.clock,PA194Site32PositiveReturnExact.returnCost]
  simp only [modelNumeralOne]
  rfl
#print axioms carryValue
#print axioms modelClock
end models
end PA194Site45PositiveClockCode
