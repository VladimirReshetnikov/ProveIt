import Surreal.HahnSeries.ExponentialLogarithm
import Surreal.HahnSeries.Regroup

/-!
# The infinitesimal exponential addition law

The exponential product is the Hahn sum of a jointly strongly summable
double family. Regrouping this family by total degree reduces its sum to
the finite coefficient identity for formal exponentials. This proves the
addition law in `e:prop-infexp` without any topological convergence or
substitution at a unit.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K] [CharZero K]

omit [IsOrderedAddMonoid Γ] [CharZero K] in
/-- Positive-order Hahn series are closed under addition, including zero. -/
theorem orderTop_add_pos {x y : K⟦Γ⟧} (hx : 0 < x.orderTop) (hy : 0 < y.orderTop) :
    0 < (x + y).orderTop :=
  (lt_min hx hy).trans_le min_orderTop_le_orderTop_add

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [CharZero K] in
private theorem regroup_nat_add_apply (s : SummableFamily Γ K (ℕ × ℕ)) (n : ℕ) :
    regroup s (fun p => p.1 + p.2) n = ∑ p ∈ _root_.Finset.HasAntidiagonal.antidiagonal n, s p := by
  classical
  ext g
  rw [regroup_apply, SummableFamily.coeff_hsum]
  simp only [restrict_apply, HahnSeries.coeff_sum]
  trans ∑ᶠ p, if p.1 + p.2 = n then (s p).coeff g else 0
  · convert (finsum_subtype_eq_finsum_cond (f := fun p => (s p).coeff g)
      (fun p => p.1 + p.2 = n)) using 1
    · rfl
    · simp only [finsum_eq_if]
  calc
    (∑ᶠ p, if p.1 + p.2 = n then (s p).coeff g else 0) =
        ∑ p ∈ _root_.Finset.HasAntidiagonal.antidiagonal n, if p.1 + p.2 = n then (s p).coeff g else 0 := by
      apply finsum_eq_sum_of_support_subset
      intro p hp
      by_cases h : p.1 + p.2 = n
      · exact _root_.Finset.HasAntidiagonal.mem_antidiagonal.mpr h
      · simp [Function.mem_support, h] at hp
    _ = ∑ p ∈ _root_.Finset.HasAntidiagonal.antidiagonal n, (s p).coeff g := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [if_pos (_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp hp)]

/-- The exponential family of a sum is a regrouping of the jointly
strongly summable product family, by finite natural-number antidiagonals. -/
theorem infExpFamily_add (x y : K⟦Γ⟧) (hx : 0 < x.orderTop) (hy : 0 < y.orderTop) :
    infExpFamily (x + y) (orderTop_add_pos hx hy) =
      regroup ((infExpFamily x hx).mul (infExpFamily y hy)) (fun p => p.1 + p.2) := by
  classical
  ext1 n
  rw [regroup_nat_add_apply]
  simp only [infExpFamily_apply, SummableFamily.mul_toFun]
  have h := congrArg (PowerSeries.coeff n)
    (PowerSeries.exp_mul_exp_eq_exp_add x y)
  have hc (q : ℚ) : algebraMap ℚ K⟦Γ⟧ q = single 0 (algebraMap ℚ K q) :=
    ((HahnSeries.C : K →+* K⟦Γ⟧).map_rat_algebraMap q).symm
  simpa only [PowerSeries.coeff_mul, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, hc, mul_comm] using h.symm

/-- Infinitesimal exponentiation converts addition to multiplication. -/
theorem infExp_add (x y : K⟦Γ⟧) (hx : 0 < x.orderTop) (hy : 0 < y.orderTop) :
    infExp (x + y) (orderTop_add_pos hx hy) = infExp x hx * infExp y hy := by
  rw [← infExpFamily_hsum (x + y) (orderTop_add_pos hx hy),
    infExpFamily_add x y hx hy, hsum_regroup, SummableFamily.hsum_mul]
  rfl

@[simp] theorem infExp_zero :
    infExp (0 : K⟦Γ⟧) (by simp) = 1 := by
  apply mul_left_cancel₀ (infExp_ne_zero (0 : K⟦Γ⟧) (by simp))
  simpa using (infExp_add (0 : K⟦Γ⟧) 0 (by simp) (by simp)).symm

/-- Negating an infinitesimal inverts its exponential. -/
theorem infExp_neg (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    infExp (-x) (by simpa using hx) = (infExp x hx)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa using (infExp_add (-x) x (by simpa using hx) hx).symm

omit [CharZero K] in
/-- The additive group of infinitesimal Hahn series. Its zero is included
because zero has order infinity. -/
def positiveOrderAddSubgroup (Γ K : Type*) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Field K] : AddSubgroup K⟦Γ⟧ where
  carrier := {x | 0 < x.orderTop}
  zero_mem' := by simp
  add_mem' := orderTop_add_pos
  neg_mem' hx := by simpa using hx

omit [CharZero K] in
@[simp] theorem mem_positiveOrderAddSubgroup (x : K⟦Γ⟧) :
    x ∈ positiveOrderAddSubgroup Γ K ↔ 0 < x.orderTop := Iff.rfl

/-- Infinitesimal exponential and logarithm form a group isomorphism:
addition at zero corresponds to multiplication at one. -/
def infExpEquiv : Multiplicative (positiveOrderAddSubgroup Γ K) ≃*
    orderTopSubOnePos Γ K where
  toFun x := toOrderTopSubOnePos (infExp_sub_one_pos x.toAdd.val x.toAdd.property)
  invFun u := Multiplicative.ofAdd
    ⟨infLog ((u.val : K⟦Γ⟧) - 1) u.property, infLog_orderTop_pos _ _⟩
  left_inv x := by
    apply Subtype.ext
    exact infLog_infExp_sub_one x.toAdd.val x.toAdd.property
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    change infExp (infLog ((u.val : K⟦Γ⟧) - 1) u.property) _ = (u.val : K⟦Γ⟧)
    rw [infExp_infLog, add_sub_cancel]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact infExp_add x.toAdd.val y.toAdd.val x.toAdd.property y.toAdd.property

@[simp] theorem infExpEquiv_apply (x : Multiplicative (positiveOrderAddSubgroup Γ K)) :
    ((infExpEquiv x).val : K⟦Γ⟧) = infExp x.toAdd.val x.toAdd.property := rfl

@[simp] theorem infExpEquiv_symm_apply (u : orderTopSubOnePos Γ K) :
    (infExpEquiv.symm u).toAdd.val = infLog ((u.val : K⟦Γ⟧) - 1) u.property := rfl

end
end Surreal.HahnSeries
