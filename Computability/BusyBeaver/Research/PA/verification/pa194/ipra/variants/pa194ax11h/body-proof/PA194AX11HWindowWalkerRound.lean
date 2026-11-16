import PA194AX11HWindowDrain
import PA194ModelCantorWalker
import PA194DiagonalLink

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194WindowWalker
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation PA194SourceFetchLoop
open PA194SourceFetchRestoreLoop PA194DiagonalIteration PA194IteratedSimulation PA194ClockInvariantDefinable
open PA194ModelMPDrain PA194DiagonalLink PA194MachineProjections PA194ModelCantorWalker PA194WindowDrain
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem oneStepAt (code : Code 1) (lower bound site : Nat) (hagrees : AgreesWindow (M := M) code lower bound)
    (hsiteLo : lower ≤ site) (hsite : site < bound) (args : Fin 11 → M) (tail : M) {t : M}
    (h : F step ![sourceState site args tail] = t) :
    PA194PausedReach.Reaches code (sourceState site args tail) t := by
  apply PA194PausedReach.oneStep code
  rw [hagrees site hsiteLo hsite args tail]
  exact h

theorem round (code : Code 1) (lower bound base : Nat)
    (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hbelow : base+7 < bound) (r : Fin 9) (rows : Rows base r) (hr6 : r ≠ 6) (hr7 : r ≠ 7)
    (a : Fin 11 → M) (tail w : M) (hw : a (location r) = w+1) :
    let d := F PA194DiagonalCode.next ![pair (a 6) (a 7)]
    PA194PausedReach.Reaches code (sourceState base a tail) (sourceState base (argsAt r a (pi₁ d) (pi₂ d) w) tail) := by
  let a1 := write r a w
  let a2 := write 7 a1 (a 7+1)
  have a16 : a1 6 = a 6 := writeOther r 6 a w (Ne.symm hr6)
  have a17 : a1 7 = a 7 := writeOther r 7 a w (Ne.symm hr7)
  have a26 : a2 6 = a 6 := by simpa only [a2,write,Function.update_of_ne (by decide : (6 : Fin 11) ≠ location 7)] using a16
  have a27 : a2 7 = a 7+1 := by simp [a2,write,show location (7 : Fin 9) = 7 from rfl]
  have start := sourceDecPositive base (base+1) r (some (base+8)) (by have := rows.valid; omega)
    rows.input a tail w hw
  have ny := sourceInc (base+1) (base+2) 7 (by have := rows.valid; omega) rows.advanceY a1 tail
  change F step ![sourceState (base+1) a1 tail] = sourceState (base+2) (write 7 a1 (a1 7+1)) tail at ny
  rw [a17] at ny
  have hprefix : PA194PausedReach.Reaches code (sourceState base a tail) (sourceState (base+2) a2 tail) :=
    PA194PausedReach.append code (oneStepAt code lower bound base hagrees (by omega) (by omega) a tail start) (oneStepAt code lower bound (base+1) hagrees (by omega) (by omega) a1 tail ny)
  dsimp only
  rcases zero_or_succ (a 6) with hz | ⟨x,hx⟩
  · rw [hz,PA194DiagonalCode.nextZero,pi₁_pair,pi₂_pair]
    have ha : regsOfArgs a2 6 = (0 : M) := a26.trans hz
    have ts := sourceDecZero (base+2) (base+4) 6 (some (base+3)) (by have := rows.valid; omega)
      rows.testX a2 tail ha
    have inside : SafeIncrements lower bound (base+4) (base+5) [6] :=
      .inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.advanceX
        (.jump _ (by have := rows.valid; omega) (by omega) (by omega) rows.repeatY)
    let out := argsAfter a2 7 [6] (a2 7)
    have td := PA194WindowDrain.drain code lower bound hagrees (base+4) (base+5) (base+7) 7 [6] (by have := rows.valid; omega) (by omega) (by omega)
      rows.drainY inside (by decide) a2 tail
    have te := sourceJump (base+7) base rows.valid rows.repeatInput out tail
    have hOut : out = argsAt r a (a 7+1) 0 w := by
      funext i
      by_cases h6 : i = 6
      · subst i
        simp [out,argsAfter,tally,a26,hz,a27,argsAt,write,
          show location (6 : Fin 9) = 6 from rfl, show location (7 : Fin 9) = 7 from rfl,
          PA194StateOne.modelNumeralOne]
      · by_cases h7 : i = 7
        · subst i
          simp [out,argsAfter,argsAt,write,PA194ModelMPDrain.subSelf,
            show location (7 : Fin 9) = 7 from rfl]
        · simp [out,argsAfter,tally,argsAt,a2,write,h6,h7,
            show location (6 : Fin 9) = 6 from rfl, show location (7 : Fin 9) = 7 from rfl,
            show modelNumeral M 0 = (0:M) from rfl, Ne.symm h6]
          rfl
    rw [←hOut]
    exact PA194PausedReach.append code (PA194PausedReach.append code (PA194PausedReach.append code hprefix (oneStepAt code lower bound (base+2) hagrees (by omega) (by omega) a2 tail ts)) td) (oneStepAt code lower bound (base+7) hagrees (by omega) (by omega) out tail te)
  · rw [hx,PA194DiagonalCode.nextPositive,pi₁_pair,pi₂_pair]
    let out := write 6 a2 x
    have ha : regsOfArgs a2 6 = x+1 := a26.trans hx
    have ts := sourceDecPositive (base+2) (base+3) 6 (some (base+4))
      (by have := rows.valid; omega) rows.testX a2 tail x ha
    have tj := sourceJump (base+3) (base+7) (by have := rows.valid; omega) rows.pass out tail
    have tk := sourceJump (base+7) base rows.valid rows.repeatInput out tail
    have hOut : out = argsAt r a x (a 7+1) w := by
      exact Function.update_comm (by decide : location (7 : Fin 9) ≠ location 6) _ _ _
    rw [←hOut]
    exact PA194PausedReach.append code (PA194PausedReach.append code (PA194PausedReach.append code hprefix (oneStepAt code lower bound (base+2) hagrees (by omega) (by omega) a2 tail ts)) (oneStepAt code lower bound (base+3) hagrees (by omega) (by omega) out tail tj)) (oneStepAt code lower bound (base+7) hagrees (by omega) (by omega) out tail tk)


#print axioms round
end models
end PA194WindowWalker
