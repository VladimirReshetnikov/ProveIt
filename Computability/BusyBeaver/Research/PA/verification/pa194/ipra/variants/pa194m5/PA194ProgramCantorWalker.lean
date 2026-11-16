import PA194ProgramDrain
import PA194ModelCantorWalker
import PA194DiagonalLink

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194ProgramCantorWalker
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SchedulerFetchPositive PA194DiagonalIteration PA194IteratedSimulation PA194ClockInvariantDefinable
open PA194ProgramDrain PA194DiagonalLink PA194MachineProjections
open PA194ModelMPDrain (location argsAfter tally subByDef frameDef)
open PA194ModelCantorWalker (write argsAt writeOther writeXY overwrite writeBack projectionDefs)
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

structure Rows (program : Program) (base : Nat) (r : Fin 9) : Prop where
  valid : base+7 < program.length
  input : row program base = some (.dec r (some (base+8)) (some (base+1)))
  advanceY : row program (base+1) = some (.inc 7 (some (base+2)))
  testX : row program (base+2) = some (.dec 6 (some (base+4)) (some (base+3)))
  pass : row program (base+3) = some (.jump (some (base+7)))
  drainY : row program (base+4) = some (.dec 7 (some (base+7)) (some (base+5)))
  advanceX : row program (base+5) = some (.inc 6 (some (base+6)))
  repeatY : row program (base+6) = some (.jump (some (base+4)))
  repeatInput : row program (base+7) = some (.jump (some base))

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
variable (program : Program)

/-- One complete Cantor diagonal advance in the literal source controller. -/
theorem round (base : Nat) (r : Fin 9) (rows : Rows program base r) (hr6 : r ≠ 6) (hr7 : r ≠ 7)
    (a : Fin 11 → M) (tail w : M) (hw : a (location r) = w+1) :
    let d := F PA194DiagonalCode.next ![pair (a 6) (a 7)]
    Reaches program (sourceState base a tail) (sourceState base (argsAt r a (pi₁ d) (pi₂ d) w) tail) := by
  let a1 := write r a w
  let a2 := write 7 a1 (a 7+1)
  have a16 : a1 6 = a 6 := writeOther r 6 a w (Ne.symm hr6)
  have a17 : a1 7 = a 7 := writeOther r 7 a w (Ne.symm hr7)
  have a26 : a2 6 = a 6 := by simpa only [a2,write,Function.update_of_ne (by decide : (6 : Fin 11) ≠ location 7)] using a16
  have a27 : a2 7 = a 7+1 := by simp [a2,write,show location (7 : Fin 9) = 7 from rfl]
  have start := PA194ProgramDrain.sourceDecPositive program base (base+1) r (some (base+8)) (by have := rows.valid; omega)
    rows.input a tail w hw
  have ny := PA194ProgramDrain.sourceInc program (base+1) (base+2) 7 (by have := rows.valid; omega) rows.advanceY a1 tail
  change F (step program) ![sourceState (base+1) a1 tail] = sourceState (base+2) (write 7 a1 (a1 7+1)) tail at ny
  rw [a17] at ny
  have hprefix : Reaches program (sourceState base a tail) (sourceState (base+2) a2 tail) :=
    PA194ProgramDrain.append program (PA194ProgramDrain.oneStep program start).reaches (PA194ProgramDrain.oneStep program ny).reaches
  dsimp only
  rcases zero_or_succ (a 6) with hz | ⟨x,hx⟩
  · rw [hz,PA194DiagonalCode.nextZero,pi₁_pair,pi₂_pair]
    have ha : regsOfArgs a2 6 = (0 : M) := a26.trans hz
    have ts := PA194ProgramDrain.sourceDecZero program (base+2) (base+4) 6 (some (base+3)) (by have := rows.valid; omega)
      rows.testX a2 tail ha
    have inside : Increments program (base+4) (base+5) [6] :=
      .inc _ _ _ _ (by have := rows.valid; omega) rows.advanceX
        (.jump _ (by have := rows.valid; omega) rows.repeatY)
    let out := argsAfter a2 7 [6] (a2 7)
    have td := PA194ProgramDrain.drain program (base+4) (base+5) (base+7) 7 [6] (by have := rows.valid; omega)
      rows.drainY inside (by decide) a2 tail
    have te := PA194ProgramDrain.sourceJump program (base+7) base rows.valid rows.repeatInput out tail
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
    exact PA194ProgramDrain.append program (PA194ProgramDrain.append program (PA194ProgramDrain.append program hprefix (PA194ProgramDrain.oneStep program ts).reaches) td.reaches) (PA194ProgramDrain.oneStep program te).reaches
  · rw [hx,PA194DiagonalCode.nextPositive,pi₁_pair,pi₂_pair]
    let out := write 6 a2 x
    have ha : regsOfArgs a2 6 = x+1 := a26.trans hx
    have ts := PA194ProgramDrain.sourceDecPositive program (base+2) (base+3) 6 (some (base+4))
      (by have := rows.valid; omega) rows.testX a2 tail x ha
    have tj := PA194ProgramDrain.sourceJump program (base+3) (base+7) (by have := rows.valid; omega) rows.pass out tail
    have tk := PA194ProgramDrain.sourceJump program (base+7) base rows.valid rows.repeatInput out tail
    have hOut : out = argsAt r a x (a 7+1) w := by
      exact Function.update_comm (by decide : location (7 : Fin 9) ≠ location 6) _ _ _
    rw [←hOut]
    exact PA194ProgramDrain.append program (PA194ProgramDrain.append program (PA194ProgramDrain.append program hprefix (PA194ProgramDrain.oneStep program ts).reaches) (PA194ProgramDrain.oneStep program tj).reaches) (PA194ProgramDrain.oneStep program tk).reaches


private theorem tupleDef (r : Fin 9) (a : Fin 11 → M) (x y left : M → M)
    (hx : 𝚺₁-Function₁ x) (hy : 𝚺₁-Function₁ y) (hl : 𝚺₁-Function₁ left) (i : Fin 11) :
    𝚺₁-Function₁ (fun j => argsAt r a (x j) (y j) (left j) i) := by
  unfold argsAt write
  by_cases hi : i = location 7
  · subst i
    simpa only [Function.update_self] using hy
  · by_cases hj : i = location 6
    · subst i
      simpa only [Function.update_of_ne hi,Function.update_self] using hx
    · by_cases hk : i = location r
      · subst i
        simpa only [Function.update_of_ne hi,Function.update_of_ne hj,Function.update_self] using hl
      · simp only [Function.update_of_ne hi,Function.update_of_ne hj,Function.update_of_ne hk]
        definability

/-- Decode one input counter with the literal eight-row diagonal walker.
The two output coordinates are the scheduler's exact projection codes. -/
theorem walk (base : Nat) (r : Fin 9) (rows : Rows program base r) (hr6 : r ≠ 6) (hr7 : r ≠ 7)
    (a : Fin 11 → M) (tail : M) :
    let n := a (location r)
    let c := cantor (a 6) (a 7)+n
    ReachesPositive program (sourceState base a tail)
      (sourceState (base+8) (argsAt r a (F fixedFirst ![c]) (F fixedSecond ![c]) 0) tail) := by
  let n := a (location r)
  let start := pair (a 6) (a 7)
  let d := fun j => F PA194DiagonalCode.run ![j,start]
  let rem := fun j => F subCode ![n,j]
  let values := fun j => argsAt r a (pi₁ (d j)) (pi₂ (d j)) (rem j)
  let frame := fun j => sourceState base (values j) tail
  have hd : 𝚺₁-Function₁ d := bindBinary _ start (binaryCodeDef PA194DiagonalCode.run)
  obtain ⟨hx,hy⟩ := projectionDefs d hd
  have hrem : 𝚺₁-Function₁ rem := subByDef n
  have hf : 𝚺₁-Function₁ frame :=
    frameDef base (fun i j => values j i) tail (tupleDef r a _ _ rem hx hy hrem)
  have move (j : M) (hj : j < n) : Reaches program (frame j) (frame (j+1)) := by
    obtain ⟨w,hw⟩ := le_iff_exists_add.mp (lt_iff_succ_le.mp hj)
    have hbefore : rem j = w+1 := by
      change F subCode ![n,j] = w+1
      rw [hw,show (j+1)+w = j+(w+1) by ac_rfl]
      exact modelSubAdd j (w+1)
    have hafter : rem (j+1) = w := by
      change F subCode ![n,j+1] = w
      rw [hw]
      exact modelSubAdd (j+1) w
    have ⟨hx,hy,hl⟩ := writeXY r hr6 hr7 a (pi₁ (d j)) (pi₂ (d j)) (rem j)
    have hround := round program base r rows hr6 hr7 (values j) tail w (hl.trans hbefore)
    change Reaches program (frame j) (sourceState base (argsAt r (values j)
      (pi₁ (F PA194DiagonalCode.next ![pair (values j 6) (values j 7)]))
      (pi₂ (F PA194DiagonalCode.next ![pair (values j 6) (values j 7)])) w) tail) at hround
    change values j 6 = pi₁ (d j) at hx
    change values j 7 = pi₂ (d j) at hy
    rw [hx,hy,pair_unpair] at hround
    have hnext : d (j+1) = F PA194DiagonalCode.next ![d j] := iterSucc _ _ _
    change Reaches program (frame j) (sourceState base (argsAt r a
      (pi₁ (d (j+1))) (pi₂ (d (j+1))) (rem (j+1))) tail)
    rw [hnext,hafter]
    rw [show values j = argsAt r a (pi₁ (d j)) (pi₂ (d j)) (rem j) from rfl,
      overwrite] at hround
    exact hround
  have hrun := PA194ProgramDrain.runMany program frame n hf move n le_rfl
  have h0 : values 0 = a := by
    have hd0 : d 0 = start := iterZero _ _
    change argsAt r a (pi₁ (d 0)) (pi₂ (d 0)) (F subCode ![n,(0:M)]) = a
    rw [hd0,show F subCode ![n,(0:M)] = n from PRASubtraction.modelSubZero n]
    change argsAt r a (pi₁ (pair (a 6) (a 7))) (pi₂ (pair (a 6) (a 7))) n = a
    rw [pi₁_pair,pi₂_pair]
    exact writeBack r a
  have hz : rem n = (0 : M) := PA194ModelMPDrain.subSelf n
  let p := cantor (a 6) (a 7)+n
  have hp : F PA194DiagonalIteration.scoreCode ![start]+n = p := by
    rw [PA194DiagonalIteration.modelScore]
    simp only [start,p,pi₁_pair,pi₂_pair]
  have hcoords := iterationProjects start n
  change F fixedFirst ![F PA194DiagonalIteration.scoreCode ![start]+n] = pi₁ (d n) ∧
    F fixedSecond ![F PA194DiagonalIteration.scoreCode ![start]+n] = pi₂ (d n) at hcoords
  rw [hp] at hcoords
  have hfinal : values n = argsAt r a (F fixedFirst ![p]) (F fixedSecond ![p]) 0 := by
    change argsAt r a (pi₁ (d n)) (pi₂ (d n)) (rem n) = _
    rw [←hcoords.1,←hcoords.2,hz]
  change Reaches program (sourceState base (values 0) tail) (sourceState base (values n) tail) at hrun
  rw [h0] at hrun
  have hslot : regsOfArgs (values n) r = (0 : M) :=
    (writeXY r hr6 hr7 a _ _ _).2.2.trans hz
  have hexit := PA194ProgramDrain.sourceDecZero program base (base+8) r (some (base+1))
    (by have := rows.valid; omega) rows.input (values n) tail hslot
  have h := PA194ProgramDrain.appendPositive program hrun (PA194ProgramDrain.oneStep program hexit)
  rw [hfinal] at h
  exact h

#print axioms round
#print axioms walk
end models
end PA194ProgramCantorWalker
