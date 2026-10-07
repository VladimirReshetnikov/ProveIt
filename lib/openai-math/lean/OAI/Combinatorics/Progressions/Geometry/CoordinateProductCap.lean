import Mathlib.Data.Fintype.BigOperators
import OAI.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def coordinateJoin {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) (x : X) : D → X :=
  fun d => if h : d = j then x else tail ⟨d,h⟩

@[simp] theorem coordinateJoin_pivot {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) (x : X) : coordinateJoin j tail x j = x := by
  simp [coordinateJoin]

@[simp] theorem coordinateJoin_other {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) (x : X) (d : {d : D // d ≠ j}) :
    coordinateJoin j tail x d.val = tail d := by
  simp [coordinateJoin, d.property]

theorem coordinateJoin_eta {D X : Type*} [DecidableEq D] (j : D) (z : D → X) :
    coordinateJoin j (fun d => z d.val) (z j) = z := by
  funext d
  by_cases h : d = j <;> simp [coordinateJoin, h]

theorem coordinateJoin_injective {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) : Function.Injective (coordinateJoin j tail) := by
  intro x y h
  simpa only [coordinateJoin_pivot] using congrFun h j

theorem independentProductPMF_coordinate_split {D X : Type*} [Fintype D] [DecidableEq D]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : D → PMF X) (j : D) :
    independentProductPMF p =
      (independentProductPMF (fun d : {d : D // d ≠ j} => p d.val)).bind
        (fun tail => (p j).map (coordinateJoin j tail)) := by
  ext z
  let tail := fun d : {d : D // d ≠ j} => z d.val
  have hz : coordinateJoin j tail (z j) = z := coordinateJoin_eta j z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (coordinateJoin_injective j tail)]
    simp only [independentProductPMF_apply]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
    simp only [coordinateJoin_pivot, coordinateJoin_other]
    exact mul_comm _ _
  · intro other hother
    have hr : coordinateJoin j tail (z j) ∉ Set.range (coordinateJoin j other) := by
      rintro ⟨x, he⟩
      apply hother
      funext d
      simpa only [coordinateJoin_other] using congrFun he d.val
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

theorem independentProductPMF_coordinate_cap {D X Y : Type*} [Fintype D] [DecidableEq D]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : D → PMF X) (j : D) (f : (D → X) → Y)
    (hf : ∀ tail, Function.Injective (fun x => f (coordinateJoin j tail x)))
    {C : ℝ} (hC : 0 ≤ C) (hp : ∀ x, (p j x).toReal ≤ C) (y : Y) :
    ((independentProductPMF p).map f y).toReal ≤ C := by
  rw [independentProductPMF_coordinate_split p j, PMF.map_bind]
  simp_rw [PMF.map_comp]
  exact pmf_bind_injective_toReal_cap _ _ _ hf hC hp y

theorem shiftedSmoothProductPMF_coordinate_cap {D Y : Type*} [Fintype D] [DecidableEq D]
    (a S : D → ℝ) (hS : ∀ d, 0 < S d) (hZ : 0 < shiftedSmoothProductMass a S)
    (j : D) (f : (D → ℤ) → Y)
    (hf : ∀ tail, Function.Injective (fun x => f (coordinateJoin j tail x)))
    (hscale : 8*(probabilityProfileLipschitz : ℝ) ≤ S j) (y : Y) :
    ((shiftedSmoothProductPMF a S hS hZ).map f y).toReal ≤ 2/S j := by
  rw [shiftedSmoothProductPMF_eq_independent]
  exact independentProductPMF_coordinate_cap _ j f hf (div_nonneg (by norm_num) (hS j).le)
    (fun x => shiftedSmoothCoefficientPMF_le (a j) hscale x) y

end Erdos3

end

end OAI
