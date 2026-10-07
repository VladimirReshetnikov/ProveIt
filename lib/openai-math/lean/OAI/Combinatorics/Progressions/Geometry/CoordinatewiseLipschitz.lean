import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem lipschitzWith_of_coordinatewise {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)] {Y : Type*} [PseudoMetricSpace Y]
    (f : (∀ i, X i) → Y) (C : ι → ℝ≥0)
    (h : ∀ i x, LipschitzWith (C i) (fun a => f (Function.update x i a))) :
    LipschitzWith (∑ i, C i) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let z (S : Finset ι) : ∀ i, X i := fun i => if i ∈ S then x i else y i
  have hbound (S : Finset ι) : dist (f (z S)) (f y) ≤ ∑ i ∈ S, (C i : ℝ) * dist (x i) (y i) := by
    induction S using Finset.induction_on with
    | empty => simp only [z, Finset.notMem_empty, ite_false, Finset.sum_empty, dist_self, le_refl]
    | @insert i S hi ih =>
      have heq : z (insert i S) = Function.update (z S) i (x i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [z, Finset.mem_insert_self, ite_true, Function.update_self]
        · simp only [z, Finset.mem_insert, hji, false_or, Function.update_of_ne hji]
      have hold : z S = Function.update (z S) i (y i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [z, hi, ite_false, Function.update_self]
        · rw [Function.update_of_ne hji]
      have hstep : dist (f (z (insert i S))) (f (z S)) ≤ (C i : ℝ) * dist (x i) (y i) := by
        calc
          _ = dist (f (Function.update (z S) i (x i))) (f (Function.update (z S) i (y i))) := by
            rw [heq]
            exact congrArg (fun v => dist (f (Function.update (z S) i (x i))) (f v)) hold
          _ ≤ _ := (h i (z S)).dist_le_mul _ _
      have htri : dist (f (z (insert i S))) (f y) ≤
          (C i : ℝ) * dist (x i) (y i) + ∑ j ∈ S, (C j : ℝ) * dist (x j) (y j) :=
        (dist_triangle _ _ _).trans (add_le_add hstep ih)
      simpa only [Finset.sum_insert hi] using htri
  have htotal : dist (f x) (f y) ≤ ∑ i, (C i : ℝ) * dist (x i) (y i) := by
    simpa only [z, Finset.mem_univ, ite_true] using hbound Finset.univ
  calc
    _ ≤ ∑ i, (C i : ℝ) * dist (x i) (y i) := htotal
    _ ≤ ∑ i, (C i : ℝ) * dist x y := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (C i).coe_nonneg)
    _ = ((∑ i, C i : ℝ≥0) : ℝ) * dist x y := by rw [NNReal.coe_sum, Finset.sum_mul]

theorem lipschitzWith_pi_hom_of_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, Group (G i)] [∀ i, PseudoMetricSpace (G i)]
    {H : Type*} [Group H] [PseudoMetricSpace H] [IsIsometricSMul Hᵐᵒᵖ H]
    (φ : (∀ i, G i) →* H) (C : ι → ℝ≥0)
    (h : ∀ i, LipschitzWith (C i) (fun a => φ (Pi.mulSingle i a))) :
    LipschitzWith (∑ i, C i) φ := by
  apply lipschitzWith_of_coordinatewise φ C
  intro i x
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have heq (a : G i) : Function.update x i a =
      Pi.mulSingle i a * Function.update x i 1 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same, mul_one]
    · simp only [Function.update_of_ne hji, Pi.mul_apply, Pi.mulSingle_eq_of_ne hji, one_mul]
  rw [heq a, heq b, map_mul, map_mul, dist_mul_right]
  exact (h i).dist_le_mul a b

end Erdos3

end

end OAI
