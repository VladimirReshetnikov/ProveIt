import GowersSzemeredi.Proofs16IntervalSlabProduct
import GowersSzemeredi.Proofs16FibreGeometry

/-! Exact arrangement counts and alternating values for a last-coordinate
slab. The arbitrary word on the last coordinate is constant on each cube. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_slab_arrangement_isIn {N k d : Nat} [NeZero N]
    (A : Finset (ZMod N)) (R : GeneralArrangement N k d) :
    R.IsIn (lastProductSet Finset.univ A) ↔
      IsAdditiveTuple R.crossSection ∧ ∀ j, R.crossSection j ∈ A := by
  simp only [GeneralArrangement.IsIn, GeneralArrangement.vertex, lastProductSet,
    Finset.mem_filter, Finset.mem_univ, true_and, section16Last_appendCoordinate]
  exact and_congr_right fun _ =>
    ⟨fun h j => h (fun _ => false) j, fun h _ j => h j⟩

/-- All base and side vectors are free; only the last coordinates obey an
additive constraint. This identity also covers zero cube dimension. -/
theorem section16_slab_arrangement_count {N k d : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    generalArrangementCount d (lastProductSet (Finset.univ : Finset (Point N k)) A) =
      N ^ ((2 * d + 1) * k) * additiveTupleCount d A := by
  classical
  have heq : (Finset.univ.filter fun R : GeneralArrangement N k d =>
      R.IsIn (lastProductSet Finset.univ A)) =
      (Finset.univ : Finset (Point N k)) ×ˢ
        ((Finset.univ : Finset (Fin (2 * d) → Point N k)) ×ˢ
          (Finset.univ.filter fun x : Fin (2 * d) → ZMod N =>
            (∀ j, x j ∈ A) ∧ IsAdditiveTuple x)) := by
    ext R
    simp [section16_slab_arrangement_isIn, GeneralArrangement.crossSection, and_comm]
  unfold generalArrangementCount countWhere
  rw [heq]
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Point, ZMod.card]
  unfold additiveTupleCount countWhere
  rw [← mul_assoc, ← pow_mul, ← pow_add]
  have hexp : k + k * (2 * d) = (2 * d + 1) * k := by ring
  rw [hexp]
  congr

private lemma boolWeight_cons {n : Nat} (b : Bool) (e : Fin n → Bool) :
    boolWeight (Fin.cons b e) = (if b then 1 else 0) + boolWeight e := by
  classical
  simp only [boolWeight, countWhere, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  cases b <;> simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true,
    ite_false, ite_true, zero_add]
  all_goals congr
  all_goals funext i; by_cases he : e i = true <;> simp [he]

/-- The signs of a positive-dimensional Boolean cube sum to zero. -/
theorem section16_cube_sign_sum {N k : Nat} [NeZero N] (hk : 1 ≤ k) :
    (∑ e : Fin k → Bool, (-1 : ZMod N) ^ boolWeight e) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  change (∑ p : Bool × (Fin n → Bool),
    (-1 : ZMod N) ^ boolWeight (Fin.cons p.1 p.2)) = 0
  simp [Fintype.sum_prod_type, boolWeight_cons, pow_add]

theorem section16_slab_arrangement_cubeValue {N k d : Nat} [NeZero N]
    (hk : 1 ≤ k) (f : ZMod N → ZMod N) (R : GeneralArrangement N k d)
    (j : Fin (2 * d)) :
    R.cubeValue (fun z => f (section16Last z)) j = 0 := by
  simp only [GeneralArrangement.cubeValue, GeneralArrangement.vertex,
    section16Last_appendCoordinate, ← Finset.sum_mul, section16_cube_sign_sum hk,
    zero_mul]

theorem section16_slab_arrangement_respected {N k d : Nat} [NeZero N]
    (hk : 1 ≤ k) (f : ZMod N → ZMod N) (R : GeneralArrangement N k d) :
    R.IsRespected (fun z => f (section16Last z)) := by
  simp only [GeneralArrangement.IsRespected, section16_slab_arrangement_cubeValue hk,
    IsAdditiveTuple, Finset.sum_const_zero]

theorem section16_slab_respected_arrangement_count {N k d : Nat} [NeZero N]
    (hk : 1 ≤ k) (A : Finset (ZMod N)) (f : ZMod N → ZMod N) :
    respectedGeneralArrangementCount d
      (lastProductSet (Finset.univ : Finset (Point N k)) A)
      (fun z => f (section16Last z)) =
        N ^ ((2 * d + 1) * k) * additiveTupleCount d A := by
  unfold respectedGeneralArrangementCount
  simp only [section16_slab_arrangement_respected hk, and_true]
  exact section16_slab_arrangement_count A

end LeanProofs.GowersSzemeredi
