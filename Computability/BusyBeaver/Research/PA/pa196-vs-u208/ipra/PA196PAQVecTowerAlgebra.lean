import PA196PAQVecSeqTrace
import DiophantineConsistency.ArithmeticUnaryRecursion

/-! Algebra of the arithmetic majorant iterator at arbitrary model-internal
indices, proved using its represented IΣ₁ recursion. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PAQVecTowerAlgebra
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA196PAQVecSeqTrace PRAWitnessCodeGrowth
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def iter (n seed : V) : V :=
  (boundConstruction (V := V)).result ![seed] n

private theorem iter_defined : 𝚺₁-Function₂[V] (iter : V → V → V) via boundBlueprint.resultDef :=
  DiophantineConsistency.ArithmeticUnaryRecursion.result_defined boundBlueprint boundConstruction

instance iter_definable : 𝚺₁-Function₂ (iter : V → V → V) := iter_defined.to_definable
instance iter_definable_delta : 𝚫₁-Function₂ (iter : V → V → V) :=
  iter_defined.graph_delta.to_definable

@[simp] theorem iter_zero (seed : V) : iter 0 seed = seed := by
  simp [iter, boundConstruction]

theorem iter_succ (n seed : V) :
    iter (n+1) seed = tau (iter n seed + 8) (22 * iter n seed + 22) := by
  simp [iter, PR.Construction.result_succ, boundConstruction]

theorem iter_seed_mono (a b n : V) (hab : a ≤ b) : iter n a ≤ iter n b := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hab
  case succ n ih =>
    rw [iter_succ, iter_succ]
    exact tau_mono (add_le_add ih le_rfl)
      (add_le_add (mul_le_mul' le_rfl ih) le_rfl)

theorem iter_add (m n seed : V) : iter (m+n) seed = iter n (iter m seed) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [show m+(n+1) = (m+n)+1 by ring, iter_succ, iter_succ, ih]

theorem iter_succ_increases (n seed : V) : iter n seed ≤ iter (n+1) seed := by
  rw [iter_succ]
  exact le_trans le_self_add (le_tau _ _)

theorem iter_inflationary (n seed : V) : seed ≤ iter n seed := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => exact le_trans ih (iter_succ_increases n seed)

theorem iter_index_mono (m n seed : V) (hmn : m ≤ n) : iter m seed ≤ iter n seed := by
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp hmn
  rw [iter_add]
  exact iter_inflationary k (iter m seed)

#print axioms iter_index_mono
#print axioms iter_seed_mono
#print axioms iter_add
end PA196PAQVecTowerAlgebra
