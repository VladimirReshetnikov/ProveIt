import PA194PAeqSubstUniformGrowth

/-! Numeric ingredients for a substitution fixpoint-stage bound: each recursive
child's candidate bound is strictly smaller and each parent triple fits. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PAeqSubstStageBounds
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PA196PAQVecTowerAlgebra PA194PAeqSubstUniformGrowth
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def stageBound (w p : V) : V := iter (p+2) (seed w p)
instance stageBound_definable : 𝚺₁-Function₂ (stageBound : V → V → V) := by
  unfold stageBound; definability

theorem iter_succ_strict (n z : V) : iter n z < iter (n+1) z := by
  rw [iter_succ]
  exact lt_of_le_of_lt (le_trans le_self_add le_self_add) (lt_tau _ _)

theorem same_child_lt (w p q : V) (h : q+2 ≤ p) : stageBound w q < stageBound w p := by
  have hq : q ≤ p := le_trans le_self_add h
  have hs := seed_mono w p q hq
  unfold stageBound
  calc
    iter (q+2) (seed w q) ≤ iter (q+2) (seed w p) := iter_seed_mono _ _ _ hs
    _ ≤ iter (p+1) (seed w p) := iter_index_mono _ _ _ (le_trans h le_self_add)
    _ < iter ((p+1)+1) (seed w p) := iter_succ_strict _ _
    _ = iter (p+2) (seed w p) := by congr 1; ring

theorem quant_child_lt (w p q : V) (h : q+2 ≤ p) :
    stageBound (qVec PA194PAeq.language w) q < stageBound w p := by
  have hq : q ≤ p := le_trans le_self_add h
  have hs := quant_seed_le w p q hq
  have hn : 1+(q+2) ≤ p+1 := by
    calc
      1+(q+2) = (q+2)+1 := by ring
      _ ≤ p+1 := add_le_add h le_rfl
  unfold stageBound
  calc
    iter (q+2) (seed (qVec PA194PAeq.language w) q) ≤ iter (q+2) (iter 1 (seed w p)) := iter_seed_mono _ _ _ hs
    _ = iter (1+(q+2)) (seed w p) := (iter_add 1 (q+2) (seed w p)).symm
    _ ≤ iter (p+1) (seed w p) := iter_index_mono _ _ _ hn
    _ < iter ((p+1)+1) (seed w p) := iter_succ_strict _ _
    _ = iter (p+2) (seed w p) := by congr 1; ring

theorem triple_le_bound (w p y : V) (hy : y ≤ iter (p+1) (seed w p)) :
    ⟪w,p,y⟫ + 1 ≤ stageBound w p := by
  let B := iter (p+1) (seed w p)
  have hs : seed w p ≤ B := iter_inflationary _ _
  have hw : w ≤ B := le_trans (le_trans le_self_add le_self_add) hs
  have hthree : p ≤ 3*p := by
    calc
      p ≤ p+(p+p) := le_self_add
      _ = 3*p := by ring
  have hp : p ≤ B := le_trans (le_trans (le_trans hthree le_add_self) le_self_add) hs
  have hw' : w ≤ tau (B+8) 0 := le_trans hw (le_trans le_self_add (le_tau _ _))
  have hp' : p ≤ tau (B+8) 0 := le_trans hp (le_trans le_self_add (le_tau _ _))
  have hy' : y ≤ tau (B+8) 0 := le_trans hy (le_trans le_self_add (le_tau _ _))
  have ht := code3_le_tau hw' hp' hy'
  have hb : (0:V)+2+2 ≤ 22*B+22 := by
    simpa using (le_trans (by norm_num : (2:V)+2 ≤ 22) (le_add_self (a := (22:V)) (b := 22*B)))
  have hbound := le_trans ht (tau_mono le_rfl hb)
  have heq : stageBound w p = tau (B+8) (22*B+22) := by
    unfold stageBound
    rw [show p+2 = (p+1)+1 by ring, iter_succ]
  rw [heq]
  exact hbound

#print axioms same_child_lt
#print axioms quant_child_lt
#print axioms triple_le_bound
end PA194PAeqSubstStageBounds
