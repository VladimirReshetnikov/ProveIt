import PA194Site32ZeroPathExact
import PA194Site32ClockPrefix
import DiophantineConsistency.PRATermCompilation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
namespace PA194Site32ZeroClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194StartupSentence PA194Site32PositiveClockCode
abbrev T := TermN 12

def z : T := state 0
def tailTerm : T := app2 ones (succT (v 9)) (v 10)
def q : T := app2 ones z (twice tailTerm)
def nineTerm : Fin 10 → T := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,z,twice (twice q)]
def clockTerm : T :=
  let rollback := A to4Term (A (A (num 1) (num 2)) (.func (PA194CarryFile.costCode 9) nineTerm))
  let boundary := A rollback (succT k)
  let to12 := A boundary (num 7)
  let to14 := A to12 (succT (A (succT (num 5)) (succT k)))
  let n := succT (succT (succT (succT k)))
  let c16 := A (A oneT n) (num 3)
  let rc := succT (A (A (num 5) (num 6)) (num 2))
  A (A to14 c16) (A (num 6) rc)
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

theorem valNine (e : Fin 12 → M) :
    (fun i : Fin 10 => Semiterm.val e Empty.elim (nineTerm i)) =
      PA194Site32ZeroFile.nine (fun i => e i.succ) := by
  funext i
  fin_cases i <;> simp [nineTerm,q,z,tailTerm,twice,succT,A,oneT,valApp2,valState,valOne,
    hv e,PA194Site32ZeroFile.nine,PA194Site32ZeroFile.tailWord] <;> rfl

theorem modelClock (e : Fin 12 → M) :
    F clockCode e = PA194Site32ZeroTo24Exact.clock (e 0) (fun i => e i.succ) := by
  have hn : (fun i => Semiterm.val e Empty.elim (nineTerm i)) =
      PA194Site32ZeroFile.nine (fun i => e i.succ) := valNine e
  rw [clockCode,modelCompile]
  simp only [clockTerm,A,oneT,num,succT,k,valApp2,valState,valOne,Semiterm.val_bvar,
    Semiterm.val_func,Function.comp_def,valTo4 e,hn]
  rfl
#print axioms valNine
#print axioms modelClock
end models
end PA194Site32ZeroClockCode
