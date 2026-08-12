import PolynomialFormulas.LazardInvariantModularProductCoefficientCore

/-!
# Executable and semantic modular product coefficients

This file proves that the list-count implementation used to generate the
degree-seven product matrix agrees with the finite-sum coefficient formula
used by the polynomial semantics.  The only closed computations are the
seven possible elementary-symmetric degrees.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open scoped BigOperators
open Finset
open LazardInvariantModularCounterexample
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

theorem subsetExponent_injective : Function.Injective subsetExponent := by
  intro s t h
  ext i
  have hi := congrFun h i
  simp only [subsetExponent] at hi
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

theorem eraseDups_nodup {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ l : List α, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro ha
        rw [List.mem_eraseDups] at ha
        simp at ha
      · exact eraseDups_nodup (as.filter fun b => !b == a)
termination_by l => l.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ as)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryExponents_nodup_below_seven :
    ∀ d : Fin 7, (elementaryExponents d.1).Nodup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryExponents_toFinset_below_seven :
    ∀ d : Fin 7,
      (elementaryExponents d.1).toFinset =
        (powersetCard d.1 (univ : Finset (Fin 6))).image subsetExponent := by
  decide

theorem f3OfNat_count_map_eq_sum_toFinset
    (l : List Exponent) (hl : l.Nodup)
    (f : Exponent → Exponent) (target : Exponent) :
    f3OfNat ((l.map f).count target) =
      ∑ x ∈ l.toFinset, if f x = target then 1 else 0 := by
  induction l with
  | nil => simp [f3OfNat]
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp hl).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hl).2
      have hx' : x ∉ xs.toFinset := by simpa using hx
      rw [List.map_cons, List.count_cons, List.toFinset_cons,
        Finset.sum_insert hx']
      rw [show f3OfNat
          ((xs.map f).count target + if (f x == target) = true then 1 else 0) =
          f3OfNat ((xs.map f).count target) +
            f3OfNat (if (f x == target) = true then 1 else 0) by
        simp [f3OfNat]]
      rw [ih hxs]
      by_cases h : f x = target <;> simp [h, f3OfNat, add_comm]

theorem f3OfNat_count_flatMap_eq_sum_toFinset
    (l : List Exponent) (hl : l.Nodup)
    (f : Exponent → List Exponent) (target : Exponent) :
    f3OfNat ((l.flatMap f).count target) =
      ∑ x ∈ l.toFinset, f3OfNat ((f x).count target) := by
  induction l with
  | nil => simp [f3OfNat]
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp hl).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hl).2
      have hx' : x ∉ xs.toFinset := by simpa using hx
      rw [List.flatMap_cons, List.count_append, List.toFinset_cons,
        Finset.sum_insert hx']
      rw [show f3OfNat
          ((f x).count target + (xs.flatMap f).count target) =
          f3OfNat ((f x).count target) +
            f3OfNat ((xs.flatMap f).count target) by
        simp [f3OfNat]]
      rw [ih hxs]

/-- The matrix generator's executable coefficient is exactly the semantic
coefficient of `e_d` times a cyclic orbit sum, for every relevant `d < 7`. -/
theorem productCoefficient_eq_semanticProductCoefficient
    (source target : Exponent) (d : Fin 7) :
    productCoefficient source d.1 target =
      semanticProductCoefficient source d.1 target := by
  rw [productCoefficient, productMonomials]
  rw [f3OfNat_count_flatMap_eq_sum_toFinset]
  · rw [show (cyclicOrbit source).toFinset = cyclicOrbitSupport source by rfl]
    apply Finset.sum_congr rfl
    intro a ha
    rw [f3OfNat_count_map_eq_sum_toFinset
      (elementaryExponents d.1)
      (elementaryExponents_nodup_below_seven d)]
    rw [elementaryExponents_toFinset_below_seven d]
    rw [Finset.sum_image]
    apply Finset.sum_congr rfl
    intro t ht
    congr 2
    funext i
    simp [addExponent, Nat.add_comm]
    exact subsetExponent_injective.injOn
  · exact eraseDups_nodup _

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
