import PA194PAeqSubstGraphStep
import PA196PAQVecTowerAlgebra
import PA194PAeqQVecGrowth

/-! PAeq substitutions and the iterated qVec majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace PA194PAeqSubstUniformGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PA196PAQVecTowerAlgebra PA194PAeqSubstGraphStep
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def seed (w p : V) : V := w + 3*p + 1
instance seed_definable : 𝚺₁-Function₂ (seed : V → V → V) := by
  unfold seed; definability

instance subst_definable_delta : 𝚫₁-Function₂ (subst PA194PAeq.language : V → V → V) :=
  (subst.defined (V := V) (L := PA194PAeq.language)).graph_delta.to_definable

theorem seed_mono (w p q : V) (h : q ≤ p) : seed w q ≤ seed w p := by
  exact add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl h)) le_rfl

theorem quant_seed_le (w p q : V) (h : q ≤ p) :
    seed (qVec PA194PAeq.language w) q ≤ iter 1 (seed w p) := by
  have hq := PA194PAeqQVecGrowth.qVec_le w
  have hq' := add_le_add hq (le_refl (3*q+1))
  have ht := tau_add_le (w+8) (22*w+22) (3*q+1)
  have hx : w+8+(3*q+1) ≤ seed w p+8 := by
    unfold seed
    calc
      w+8+(3*q+1) = (w+3*q+1)+8 := by ring
      _ ≤ (w+3*p+1)+8 := add_le_add (seed_mono w p q h) le_rfl
  have hd : 22*w+22 ≤ 22*(seed w p)+22 :=
    add_le_add (mul_le_mul' le_rfl (le_trans le_self_add le_self_add)) le_rfl
  have hiter : iter (1 : V) (seed w p) = tau (seed w p+8) (22*(seed w p)+22) := by
    simpa using iter_succ (0 : V) (seed w p)
  rw [hiter]
  exact le_trans (by simpa [seed, add_assoc] using hq') (le_trans ht (tau_mono hx hd))

/-- A uniform output bound for PAeq substitution at any model-internal
formula code, proved by internal Π₁ order induction. -/
theorem subst_le_uniform : ∀ p : V, IsUFormula PA194PAeq.language p → ∀ w,
    subst PA194PAeq.language w p ≤ iter (p+1) (seed w p) := by
  intro p
  induction p using ISigma1.pi1_order_induction
  · definability
  case ind p ih =>
    intro hp w
    let S := seed w p
    let B := iter p S
    have hB : w+3*p+1 ≤ B := iter_inflationary p S
    have hg : (Substs.construction (V := V) PA194PAeq.language).Graph PA194PAeq.language w p (subst PA194PAeq.language w p) :=
      (Substs.construction PA194PAeq.language).result_prop w hp
    have hchildren : ∀ w' q y', (w' = w ∨ w' = qVec PA194PAeq.language w) → q+2 ≤ p →
        (Substs.construction (V := V) PA194PAeq.language).Graph PA194PAeq.language w' q y' → y' ≤ B := by
      intro w' q y' hw' hq hgraph
      have hq' : q < p := lt_of_lt_of_le (by simp) hq
      have hvalid : IsUFormula PA194PAeq.language q := (UformulaRec1.Construction.Graph.case_iff.mp hgraph).1
      have hy : subst PA194PAeq.language w' q = y' := (Substs.construction PA194PAeq.language).result_eq_of_graph hgraph
      rw [←hy]
      rcases hw' with he | he
      · subst w'
        have hs : seed w q ≤ S := seed_mono w p q (le_trans le_self_add hq)
        have hn : q+1 ≤ p := le_trans (by simp) hq
        exact le_trans (ih q hq' hvalid w)
          (le_trans (iter_seed_mono _ _ _ hs) (iter_index_mono _ _ _ hn))
      · subst w'
        have hs : seed (qVec PA194PAeq.language w) q ≤ iter 1 S :=
          quant_seed_le w p q (le_trans le_self_add hq)
        have hn : 1+(q+1) ≤ p := by
          rw [show 1+(q+1) = q+2 by ring]
          exact hq
        exact le_trans (ih q hq' hvalid (qVec PA194PAeq.language w))
          (le_trans (iter_seed_mono _ _ _ hs)
            (le_trans (le_of_eq (iter_add 1 (q+1) S).symm) (iter_index_mono _ _ _ hn)))
    have h := graph_step w p (subst PA194PAeq.language w p) B hg hB hchildren
    simpa [B, S, iter_succ] using h

#print axioms subst_le_uniform
#print axioms quant_seed_le
end PA194PAeqSubstUniformGrowth
