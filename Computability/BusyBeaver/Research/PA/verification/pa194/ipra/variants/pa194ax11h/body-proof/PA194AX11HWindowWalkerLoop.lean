import PA194AX11HWindowWalkerRound
import PA194DiagonalLink

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194WindowWalkerLoop
open PA194WindowWalker
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

theorem walk (code : Code 1) (lower bound base : Nat)
    (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hbelow : base+7 < bound) (r : Fin 9) (rows : Rows base r) (hr6 : r ≠ 6) (hr7 : r ≠ 7)
    (a : Fin 11 → M) (tail : M) :
    let n := a (location r)
    let c := cantor (a 6) (a 7)+n
    PA194PausedReach.Reaches code (sourceState base a tail)
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
  have move (j : M) (hj : j < n) : PA194PausedReach.Reaches code (frame j) (frame (j+1)) := by
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
    have hround := PA194WindowWalker.round code lower bound base hagrees hbase hbelow r rows hr6 hr7 (values j) tail w (hl.trans hbefore)
    change PA194PausedReach.Reaches code (frame j) (sourceState base (argsAt r (values j)
      (pi₁ (F PA194DiagonalCode.next ![pair (values j 6) (values j 7)]))
      (pi₂ (F PA194DiagonalCode.next ![pair (values j 6) (values j 7)])) w) tail) at hround
    change values j 6 = pi₁ (d j) at hx
    change values j 7 = pi₂ (d j) at hy
    rw [hx,hy,pair_unpair] at hround
    have hnext : d (j+1) = F PA194DiagonalCode.next ![d j] := iterSucc _ _ _
    change PA194PausedReach.Reaches code (frame j) (sourceState base (argsAt r a
      (pi₁ (d (j+1))) (pi₂ (d (j+1))) (rem (j+1))) tail)
    rw [hnext,hafter]
    rw [show values j = argsAt r a (pi₁ (d j)) (pi₂ (d j)) (rem j) from rfl,
      overwrite] at hround
    exact hround
  have hrun := PA194PausedReach.runMany code frame n hf move n le_rfl
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
  change PA194PausedReach.Reaches code (sourceState base (values 0) tail) (sourceState base (values n) tail) at hrun
  rw [h0] at hrun
  have hslot : regsOfArgs (values n) r = (0 : M) :=
    (writeXY r hr6 hr7 a _ _ _).2.2.trans hz
  have hexit := sourceDecZero base (base+8) r (some (base+1))
    (by have := rows.valid; omega) rows.input (values n) tail hslot
  have hexit' : PA194PausedReach.Reaches code (sourceState base (values n) tail)
      (sourceState (base+8) (values n) tail) := by
    apply PA194PausedReach.oneStep code
    rw [hagrees base hbase (by omega) (values n) tail]
    exact hexit
  have h := PA194PausedReach.append code hrun hexit'
  rw [hfinal] at h
  exact h

#print axioms walk
end models
end PA194WindowWalkerLoop
