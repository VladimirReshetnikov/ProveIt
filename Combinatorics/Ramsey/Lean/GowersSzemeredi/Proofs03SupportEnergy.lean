import GowersSzemeredi.Proofs03Equivalences

/-! Uniformity energy bounds in terms of the support, independent of the
ambient modulus. These bounds retain mass when selecting nonuniform cells. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- A bounded cube product is at most its base vertex in absolute value. -/
theorem cubeDifference_norm_le_base {N k : Nat} {f : ZMod N → Complex}
    (hf : DiscValued f) (a : Point N k) (s : ZMod N) :
    ‖cubeDifference f a s‖ ≤ ‖f s‖ := by
  induction k generalizing s with
  | zero => simp [cubeDifference, iteratedDifference]
  | succ k ih =>
    have ha : a = Fin.cons (a 0) (Fin.tail a) := (Fin.cons_self_tail a).symm
    rw [ha, cubeDifference_cons, difference, norm_mul, norm_star]
    exact (mul_le_of_le_one_right (norm_nonneg _) (cubeDifference_discValued hf _ _)).trans
      (ih (Fin.tail a) s)

/-- The sum of absolute cube products is bounded by a power of the L1 mass.
Only the base vertex and the individual direction vertices are needed. -/
theorem sum_cubeDifference_norm_le_l1_pow {N k : Nat} [NeZero N]
    {f : ZMod N → Complex} (hf : DiscValued f) :
    (∑ a : Point N k, ∑ s : ZMod N, ‖cubeDifference f a s‖) ≤
      (∑ s : ZMod N, ‖f s‖) ^ (k + 1) := by
  induction k with
  | zero => simp [cubeDifference, iteratedDifference, Point]
  | succ k ih =>
    rw [sum_point_succ]
    calc
      _ ≤ ∑ r : ZMod N, ∑ a : Point N k, ∑ s : ZMod N,
          ‖cubeDifference f a s‖ * ‖f (s - r)‖ := by
        apply Finset.sum_le_sum; intro r _
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro s _
        rw [cubeDifference_cons, difference, norm_mul, norm_star]
        exact mul_le_mul_of_nonneg_left (cubeDifference_norm_le_base hf a (s - r))
          (norm_nonneg _)
      _ = (∑ a : Point N k, ∑ s : ZMod N, ‖cubeDifference f a s‖) *
          (∑ s : ZMod N, ‖f s‖) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro s _
        rw [← Finset.mul_sum]
        congr 1
        exact (Equiv.subLeft s).sum_comp (fun t => ‖f t‖)
      _ ≤ (∑ s : ZMod N, ‖f s‖) ^ (k + 1) * (∑ s : ZMod N, ‖f s‖) :=
        mul_le_mul_of_nonneg_right ih (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ = _ := (pow_succ _ (k + 1)).symm

/-- Unnormalized degree-k uniformity energy is at most the (k+2)-th power
of the L1 mass of a disc-valued function. -/
theorem uniformEnergy_le_l1_pow {N k : Nat} [NeZero N]
    {f : ZMod N → Complex} (hf : DiscValued f) :
    (∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2) ≤
      (∑ s : ZMod N, ‖f s‖) ^ (k + 2) := by
  have hnonneg : 0 ≤ ∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ = ‖∑ a : Point N (k + 1), ∑ s : ZMod N, cubeDifference f a s‖ := by
      rw [sum_cube_succ_eq_sum_norm_sq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnonneg]
    _ ≤ ∑ a : Point N (k + 1), ‖∑ s : ZMod N, cubeDifference f a s‖ := norm_sum_le _ _
    _ ≤ ∑ a : Point N (k + 1), ∑ s : ZMod N, ‖cubeDifference f a s‖ :=
      Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ ≤ _ := sum_cubeDifference_norm_le_l1_pow hf

/-- A support bound needs no progression structure or primality assumption. -/
theorem uniformEnergy_le_support_pow {N k : Nat} [NeZero N]
    {f : ZMod N → Complex} (hf : DiscValued f) (S : Finset (ZMod N))
    (hsupp : ∀ x, x ∉ S → f x = 0) :
    (∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2) ≤
      (S.card : Real) ^ (k + 2) := by
  have hl1 : (∑ x : ZMod N, ‖f x‖) ≤ (S.card : Real) := by
    calc
      _ = ∑ x ∈ S, ‖f x‖ := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro x _ hx
        simp [hsupp x hx]
      _ ≤ ∑ _x ∈ S, (1 : Real) := Finset.sum_le_sum fun x _ => hf x
      _ = _ := by simp
  exact (uniformEnergy_le_l1_pow hf).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hl1 _)

end LeanProofs.GowersSzemeredi
