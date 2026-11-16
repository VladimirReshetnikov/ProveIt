import PA194SymbolicInterpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194SymbolicAuto
open PA194BidirectionalRow PA194SymbolicTrace PA194SymbolicChecker PA194SymbolicInterpreter

def propose (s : Config) : Option Row :=
  match s.right with
  | [] => none
  | b::_ =>
    let (w,d,next) := PA194Rows.rows.getD (s.q+s.q+bit b) (0,0,194)
    some ⟨decide (w=1),decide (d=1),next⟩

def run : Nat → Config → List Row × Config
  | 0, s => ([],s)
  | fuel+1, s =>
    match propose s with
    | none => ([],s)
    | some row =>
      match checkStep s row with
      | none => ([],s)
      | some mid =>
        let (rows,t) := run fuel mid
        (row::rows,t)

theorem runSound (fuel : Nat) (s : Config) : checkRun s (run fuel s).1 = some (run fuel s).2 := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [run]
    cases hp : propose s with
    | none => rfl
    | some row =>
      simp only
      cases hs : checkStep s row with
      | none => rfl
      | some mid =>
        have hi := ih mid
        cases hr : run fuel mid with
        | mk rows t =>
          simp only [hr] at hi
          simp only [hr,Prod.fst,Prod.snd,checkRun,hs,Option.bind_some]
          exact hi

theorem runLength (fuel : Nat) (s : Config) : (run fuel s).1.length ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    simp only [run]
    cases hp : propose s with
    | none => simp [hp]
    | some row =>
      cases hs : checkStep s row with
      | none => simp [hp,hs]
      | some mid =>
        have hi := ih mid
        cases hr : run fuel mid with
        | mk rows t =>
          simp only [hr] at hi
          simpa [hp,hs,hr] using Nat.succ_le_succ hi

open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)

theorem runCorrect (fuel : Nat) (s : Config) (leftTail rightTail : M) :
    F PA194Stepper.stepper ![modelNumeral M (run fuel s).1.length,encode s leftTail rightTail] =
      encode (run fuel s).2 leftTail rightTail :=
  checkedRunCorrect _ _ _ (runSound fuel s) leftTail rightTail
#print axioms runSound
#print axioms runLength
#print axioms runCorrect
end models
end PA194SymbolicAuto
