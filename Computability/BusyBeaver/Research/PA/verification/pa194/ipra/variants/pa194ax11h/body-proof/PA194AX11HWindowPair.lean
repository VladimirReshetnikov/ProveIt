import PA194AX11HWindowDrain
import PA194ModelMPPair
import PA194DiagonalLink

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194WindowPair
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ClockInvariantDefinable
open PA194ModelMPDrain PA194TargetCantor PA194ModelMPPair
open PA194WindowDrain PA194IteratedSimulation

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


theorem drainT (code : Code 1) (lower bound base : Nat) (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hbelow : base+9 < bound) (rows : Rows base) (a : Fin 11 → M) (tail : M) :
    PA194PausedReach.Reaches code (sourceState base a tail)
      (sourceState (base+4) (values a 0 (a 6+a 1) (a 7+a 1)) tail) := by
  have path : SafeIncrements lower bound base (base+1) [7,6] :=
    .inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.increaseY
      (.inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.increaseX
        (.jump _ (by have := rows.valid; omega) (by omega) (by omega) rows.repeatT))
  have h := PA194WindowDrain.drain code lower bound hagrees base (base+1) (base+4) 1 [7,6] (by have := rows.valid; omega) (by omega) (by omega)
    rows.drainT path (by decide) a tail
  have he : argsAfter a 1 [7,6] (a (location 1)) = values a 0 (a 6+a 1) (a 7+a 1) := by
    funext i
    fin_cases i <;> simp [argsAfter,location,tally,values,subSelf,
      PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rwa [he] at h

theorem round (code : Code 1) (lower bound base : Nat) (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hbelow : base+9 < bound) (rows : Rows base) (a : Fin 11 → M) (tail x y : M) :
    PA194PausedReach.Reaches code (sourceState (base+4) (values a 0 (x+1) y) tail)
      (sourceState (base+4) (values a 0 x (y+(x+1))) tail) := by
  let a0 := values a 0 (x+1) y
  let a1 := Function.update a0 6 x
  let a2 := Function.update a1 7 (y+1)
  let a3 := values a x 0 (y+1)
  have h6 : a0 6 = x+1 := by simp [a0,values]
  have h0 := sourceDecPositive (base+4) (base+5) 6 (some (base+10)) (by have := rows.valid; omega)
    rows.reduceX a0 tail x h6
  have h1 := sourceInc (base+5) (base+6) 7 (by have := rows.valid; omega)
    rows.accumulate a1 tail
  have h7 : regsOfArgs a1 7 = y := by simp [regsOfArgs,a1,a0,values]
  rw [h7] at h1
  have path : SafeIncrements lower bound (base+6) (base+7) [1] :=
    .inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.increaseT
      (.jump _ (by have := rows.valid; omega) (by omega) (by omega) rows.repeatX)
  have h2 := PA194WindowDrain.drain code lower bound hagrees (base+6) (base+7) (base+9) 6 [1] (by have := rows.valid; omega) (by omega) (by omega)
    rows.drainX path (by decide) a2 tail
  have hr2 : argsAfter a2 6 [1] (a2 (location 6)) = a3 := by
    funext i
    fin_cases i <;> simp [argsAfter,location,tally,a3,a2,a1,a0,values,subSelf,
      PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rw [hr2] at h2
  have h3 := sourceJump (base+9) base rows.valid rows.nextPair a3 tail
  have h4 := drainT code lower bound base hagrees hbase hbelow rows a3 tail
  have hr4 : values a3 0 (a3 6+a3 1) (a3 7+a3 1) = values a 0 x (y+(x+1)) := by
    funext i
    fin_cases i <;> simp [a3,values] <;> ac_rfl
  rw [hr4] at h4
  have p0 : PA194PausedReach.Reaches code (sourceState (base+4) a0 tail) (sourceState (base+5) a1 tail) := by
    apply PA194PausedReach.oneStep code
    rw [hagrees (base+4) (by omega) (by omega) a0 tail]
    exact h0
  have p1 : PA194PausedReach.Reaches code (sourceState (base+5) a1 tail) (sourceState (base+6) a2 tail) := by
    apply PA194PausedReach.oneStep code
    rw [hagrees (base+5) (by omega) (by omega) a1 tail]
    exact h1
  have p3 : PA194PausedReach.Reaches code (sourceState (base+9) a3 tail) (sourceState base a3 tail) := by
    apply PA194PausedReach.oneStep code
    rw [hagrees (base+9) (by omega) hbelow a3 tail]
    exact h3
  exact PA194PausedReach.append code (PA194PausedReach.append code (PA194PausedReach.append code
    (PA194PausedReach.append code p0 p1) h2) p3) h4

private theorem triangleFunction : 𝚺₁-Function₁ (fun x : M => triangle x) := by
  let f := fun x : M => F fixedCantor ![x,(0 : M)]
  have hf : 𝚺₁-Function₁ f := bindBinary _ _ (binaryCodeDef fixedCantor)
  have h : f = fun x => triangle x := by
    funext x
    unfold f
    rw [modelCantorSelected fixedCantor fixedCantor_certified]
    simp [cantor]
  rwa [h] at hf

private theorem orbitDef (b : Nat) (a : Fin 11 → M) (tail n y : M)
    (r : M → M) (hr : 𝚺₁-Function₁ r) :
    𝚺₁-Predicate (fun j : M => n < j ∨ ∃ k left out : M,
      left+j = n ∧ r k = sourceState b (values a 0 left out) tail ∧
      out+triangle left = y+triangle n) := by
  haveI := hr
  haveI := triangleFunction (M := M)
  change 𝚺₁-Predicate (fun j : M => n < j ∨ ∃ k left out : M,
    left+j = n ∧ r k =
      pair (modelNumeral M b) (pair (a 0) (pair (0 : M) (pair (a 2)
        (pair (a 3) (pair (a 4) (pair (a 5) (pair left (pair out (pair (a 8) tail))))))))) ∧
    out+triangle left = y+triangle n)
  definability

/-- The pairing loop consumes X and adds its triangular number to Y. -/
theorem triangleLoop (code : Code 1) (lower bound base : Nat) (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hbelow : base+9 < bound) (rows : Rows base) (a : Fin 11 → M) (tail n y : M) :
    PA194PausedReach.Reaches code (sourceState (base+4) (values a 0 n y) tail)
      (sourceState (base+10) (values a 0 0 (y+triangle n)) tail) := by
  let initial := sourceState (base+4) (values a 0 n y) tail
  let r := fun k => F (iterate code) ![k,initial]
  have hr : 𝚺₁-Function₁ r := bindBinary _ _ (binaryCodeDef (iterate code))
  have h : ∀ j : M, n < j ∨ ∃ k left out : M,
      left+j = n ∧ r k = sourceState (base+4) (values a 0 left out) tail ∧
      out+triangle left = y+triangle n := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | hP => exact orbitDef (base+4) a tail n y r hr
    | zero =>
      have h0 : r 0 = initial := PA194IteratedSimulation.iterateZero code initial
      exact Or.inr ⟨0,n,y,add_zero _,h0,rfl⟩
    | succ j ih =>
      by_cases hb : n < j+1
      · exact Or.inl hb
      · right
        have hj : j < n := lt_of_lt_of_le (lt_add_one j) (not_lt.mp hb)
        obtain ⟨k,left,out,hleft,hreach,htri⟩ := ih.resolve_left (not_lt_of_ge (le_of_lt hj))
        rcases zero_or_succ left with hz | ⟨x,hx⟩
        · rw [hz,zero_add] at hleft
          exact (_root_.lt_irrefl _ (hleft ▸ hj)).elim
        · have rr := round code lower bound base hagrees hbase hbelow rows a tail x out
          rw [←hx] at rr
          obtain ⟨time,htime⟩ := PA194PausedReach.append code (show PA194PausedReach.Reaches code initial _ from ⟨k,hreach⟩) rr
          have hs : x+(j+1) = n := by rw [←hleft,hx]; ac_rfl
          have tr : (out+(x+1))+triangle x = y+triangle n := by
            rw [hx,triangle_succ] at htri
            rw [←htri]
            ac_rfl
          refine ⟨time,x,out+left,hs,?_,?_⟩
          · simpa only [hx] using htime
          · simpa only [hx] using tr
  obtain ⟨k,left,out,hs,ht,hy⟩ := (h n).resolve_left (_root_.lt_irrefl _)
  have hz : left = 0 := add_right_cancel (hs.trans (zero_add n).symm)
  rw [hz,show triangle (0 : M) = 0 from by simp [triangle],add_zero] at hy
  rw [hz,hy] at ht
  have hexit := sourceDecZero (base+4) (base+10) 6 (some (base+5))
    (by have := rows.valid; omega) rows.reduceX (values a 0 0 (y+triangle n)) tail
    (by simp [values,regsOfArgs])
  apply PA194PausedReach.append code (show PA194PausedReach.Reaches code initial _ from ⟨k,ht⟩)
  apply PA194PausedReach.oneStep code
  rw [hagrees (base+4) (by omega) (by omega) (values a 0 0 (y+triangle n)) tail,hexit]

/-- The ten literal source rows compute a Cantor pair into Y. -/
theorem pair (code : Code 1) (lower bound base : Nat) (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hbelow : base+9 < bound) (rows : Rows base) (a : Fin 11 → M) (tail : M) (hY : a 7 = 0) :
    PA194PausedReach.Reaches code (sourceState base a tail)
      (sourceState (base+10) (values a 0 0 (cantor (a 6) (a 1))) tail) := by
  have h1 := drainT code lower bound base hagrees hbase hbelow rows a tail
  rw [hY,zero_add] at h1
  have h2 := triangleLoop code lower bound base hagrees hbase hbelow rows a tail (a 6+a 1) (a 1)
  have ha : a 1+triangle (a 6+a 1) = cantor (a 6) (a 1) := by
    unfold cantor
    ac_rfl
  rw [ha] at h2
  exact PA194PausedReach.append code h1 h2

#print axioms triangleLoop
#print axioms pair
end models
end PA194WindowPair
