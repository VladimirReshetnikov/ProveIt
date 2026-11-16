import PA194ModelMPDrain
import PA194DiagonalLink

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace PA194ModelMPPair
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194SourceFetchRestoreLoop PA194ClockInvariantDefinable
open PA194ModelMPDrain PA194TargetCantor

structure Rows (base : Nat) : Prop where
  valid : base+9 < 3673
  drainT : row base = some (.dec 1 (some (base+4)) (some (base+1)))
  increaseY : row (base+1) = some (.inc 7 (some (base+2)))
  increaseX : row (base+2) = some (.inc 6 (some (base+3)))
  repeatT : row (base+3) = some (.jump (some base))
  reduceX : row (base+4) = some (.dec 6 (some (base+10)) (some (base+5)))
  accumulate : row (base+5) = some (.inc 7 (some (base+6)))
  drainX : row (base+6) = some (.dec 6 (some (base+9)) (some (base+7)))
  increaseT : row (base+7) = some (.inc 1 (some (base+8)))
  repeatX : row (base+8) = some (.jump (some (base+6)))
  nextPair : row (base+9) = some (.jump (some base))

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

def values (a : Fin 11 → M) (t x y : M) : Fin 11 → M :=
  Function.update (Function.update (Function.update a 1 t) 6 x) 7 y

theorem drainT (base : Nat) (rows : Rows base) (a : Fin 11 → M) (tail : M) :
    ReachesPositive (sourceState base a tail)
      (sourceState (base+4) (values a 0 (a 6+a 1) (a 7+a 1)) tail) := by
  have path : Increments base (base+1) [7,6] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.increaseY
      (.inc _ _ _ _ (by have := rows.valid; omega) rows.increaseX
        (.jump _ (by have := rows.valid; omega) rows.repeatT))
  have h := drain base (base+1) (base+4) 1 [7,6] (by have := rows.valid; omega)
    rows.drainT path (by decide) a tail
  have he : argsAfter a 1 [7,6] (a (location 1)) = values a 0 (a 6+a 1) (a 7+a 1) := by
    funext i
    fin_cases i <;> simp [argsAfter,location,tally,values,subSelf,
      PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rwa [he] at h

theorem round (base : Nat) (rows : Rows base) (a : Fin 11 → M) (tail x y : M) :
    Reaches (sourceState (base+4) (values a 0 (x+1) y) tail)
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
  have path : Increments (base+6) (base+7) [1] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.increaseT
      (.jump _ (by have := rows.valid; omega) rows.repeatX)
  have h2 := drain (base+6) (base+7) (base+9) 6 [1] (by have := rows.valid; omega)
    rows.drainX path (by decide) a2 tail
  have hr2 : argsAfter a2 6 [1] (a2 (location 6)) = a3 := by
    funext i
    fin_cases i <;> simp [argsAfter,location,tally,a3,a2,a1,a0,values,subSelf,
      PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rw [hr2] at h2
  have h3 := sourceJump (base+9) base rows.valid rows.nextPair a3 tail
  have h4 := drainT base rows a3 tail
  have hr4 : values a3 0 (a3 6+a3 1) (a3 7+a3 1) = values a 0 x (y+(x+1)) := by
    funext i
    fin_cases i <;> simp [a3,values] <;> ac_rfl
  rw [hr4] at h4
  exact append (append (append (append (oneStep h0).reaches (oneStep h1).reaches)
    h2.reaches) (oneStep h3).reaches) h4.reaches

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
theorem triangleLoop (base : Nat) (rows : Rows base) (a : Fin 11 → M) (tail n y : M) :
    ReachesPositive (sourceState (base+4) (values a 0 n y) tail)
      (sourceState (base+10) (values a 0 0 (y+triangle n)) tail) := by
  let initial := sourceState (base+4) (values a 0 n y) tail
  let r := fun k => F run ![k,initial]
  have hr : 𝚺₁-Function₁ r := bindBinary _ _ (binaryCodeDef run)
  have h : ∀ j : M, n < j ∨ ∃ k left out : M,
      left+j = n ∧ r k = sourceState (base+4) (values a 0 left out) tail ∧
      out+triangle left = y+triangle n := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | hP => exact orbitDef (base+4) a tail n y r hr
    | zero =>
      have h0 : r 0 = initial := PA194IteratedSimulation.iterateZero step initial
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
        · have rr := round base rows a tail x out
          rw [←hx] at rr
          obtain ⟨time,htime⟩ := append (show Reaches initial _ from ⟨k,hreach⟩) rr
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
  exact appendPositive (show Reaches initial _ from ⟨k,ht⟩) (oneStep hexit)

/-- The ten literal source rows compute a Cantor pair into Y. -/
theorem pair (base : Nat) (rows : Rows base) (a : Fin 11 → M) (tail : M) (hY : a 7 = 0) :
    ReachesPositive (sourceState base a tail)
      (sourceState (base+10) (values a 0 0 (cantor (a 6) (a 1))) tail) := by
  have h1 := drainT base rows a tail
  rw [hY,zero_add] at h1
  have h2 := triangleLoop base rows a tail (a 6+a 1) (a 1)
  have ha : a 1+triangle (a 6+a 1) = cantor (a 6) (a 1) := by
    unfold cantor
    ac_rfl
  rw [ha] at h2
  exact appendPositive h1.reaches h2

#print axioms triangleLoop
#print axioms pair
end models
end PA194ModelMPPair
