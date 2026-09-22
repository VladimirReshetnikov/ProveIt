import Surreal.Algebra.Modulus
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Multiset.Fintype
import Mathlib.Analysis.Convex.Combination

/-!
# Gauss--Lucas over the ordered base field

The finite barycentric identity `polynomial:eq:barycentric` and the
Gauss--Lucas assertions of `polynomial:thm:gausslucas` in
`docs/surcomplex/polynomial-algebra/article.tex`. Root occurrences, rather
than distinct root values, index the sums, retaining every multiplicity.
The weights and the convex hull use the ordered field `F`, with no
Archimedean or topological assumption. Splitting is an explicit hypothesis,
including for the intermediate polynomials in the higher-derivative theorem.
-/

noncomputable section

namespace Surreal.FinitePolynomial

open Polynomial Finset Surreal.Complexify

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [HasNonnegSquareRoots F]

local instance polynomialGaussLucasDecidableEq : DecidableEq (Complexify F) := Classical.decEq _

/-- The positive inverse-square weight for a single root occurrence.
Summing occurrences repeats the weight according to root multiplicity. -/
def criticalRootWeight (p : (Complexify F)[X]) (w : Complexify F) (a : p.roots) : F :=
  (modulus (w - (a : Complexify F)) ^ 2)⁻¹

/-- The denominator of the finite barycentric expression. -/
def criticalWeightTotal (p : (Complexify F)[X]) (w : Complexify F) : F :=
  ∑ a : p.roots, criticalRootWeight p w a

/-- Weights normalized to have total one. -/
def normalizedCriticalRootWeight (p : (Complexify F)[X]) (w : Complexify F)
    (a : p.roots) : F := criticalRootWeight p w a / criticalWeightTotal p w

/-- At a nonroot, every individual barycentric weight is strictly positive. -/
theorem criticalRootWeight_pos (p : (Complexify F)[X]) {w : Complexify F}
    (hw : p.eval w ≠ 0) (a : p.roots) : 0 < criticalRootWeight p w a := by
  have ha : p.IsRoot (a : Complexify F) := isRoot_of_mem_roots Multiset.coe_mem
  have hwa : w - (a : Complexify F) ≠ 0 := by
    intro h
    exact hw ((sub_eq_zero.mp h) ▸ ha)
  exact inv_pos.mpr (pow_pos (modulus_pos hwa) 2)

/-- Positive degree and splitting make the total weight strictly positive. -/
theorem criticalWeightTotal_pos (p : (Complexify F)[X]) (hn : 0 < p.natDegree)
    (hs : p.Splits) {w : Complexify F} (hw : p.eval w ≠ 0) :
    0 < criticalWeightTotal p w := by
  have hcard : 0 < Fintype.card p.roots := by
    rw [Multiset.card_coe, ← hs.natDegree_eq_card_roots]
    exact hn
  letI : Nonempty p.roots := Fintype.card_pos_iff.mp hcard
  exact sum_pos (fun a _ => criticalRootWeight_pos p hw a) univ_nonempty

/-- Conjugating the inverse produces the positive inverse-square coefficient. -/
theorem star_inv_eq_modulus_sq_smul (z : Complexify F) :
    star (z⁻¹) = (modulus z ^ 2)⁻¹ • z := by
  rw [inv_eq_modulus]
  ext <;> simp

/-- The logarithmic derivative at a nonroot critical point, conjugated and
written as a finite weighted sum of differences. -/
theorem critical_weighted_difference_sum_eq_zero (p : (Complexify F)[X])
    (hs : p.Splits) {w : Complexify F} (hw : p.eval w ≠ 0)
    (hd : p.derivative.eval w = 0) :
    ∑ a : p.roots, criticalRootWeight p w a • (w - (a : Complexify F)) = 0 := by
  have hlog : (p.roots.map fun a => (w - a)⁻¹).sum = 0 := by
    simpa [hd, one_div] using (hs.eval_derivative_div_eval_of_ne_zero hw).symm
  have hsum : (∑ a : p.roots, (w - (a : Complexify F))⁻¹) = 0 := by
    calc
      _ = (p.roots.map fun a => (w - a)⁻¹).sum :=
        congrArg Multiset.sum (Multiset.map_univ p.roots (fun a => (w - a)⁻¹))
      _ = 0 := hlog
  calc
    _ = (starRingEnd (Complexify F)) (∑ a : p.roots, (w - (a : Complexify F))⁻¹) := by
      rw [map_sum]
      apply sum_congr rfl
      intro a _
      exact (star_inv_eq_modulus_sq_smul (w - (a : Complexify F))).symm
    _ = 0 := by rw [hsum, map_zero]

/-- The exact occurrence-indexed barycentric formula: the inverse of the
positive total weight scales the weighted root sum. Grouping equal roots
recovers the displayed multiplicities in `polynomial:eq:barycentric`. -/
theorem critical_point_eq_barycentric (p : (Complexify F)[X]) (hn : 0 < p.natDegree)
    (hs : p.Splits) {w : Complexify F} (hw : p.eval w ≠ 0)
    (hd : p.derivative.eval w = 0) :
    w = (criticalWeightTotal p w)⁻¹ •
      ∑ a : p.roots, criticalRootWeight p w a • (a : Complexify F) := by
  have h := critical_weighted_difference_sum_eq_zero p hs hw hd
  simp only [smul_sub, sum_sub_distrib, ← sum_smul, sub_eq_zero] at h
  have htotal : criticalWeightTotal p w ≠ 0 := (criticalWeightTotal_pos p hn hs hw).ne'
  calc
    w = (criticalWeightTotal p w)⁻¹ • (criticalWeightTotal p w • w) :=
      (inv_smul_smul₀ htotal w).symm
    _ = _ := congrArg ((criticalWeightTotal p w)⁻¹ • ·) h

/-- Every normalized barycentric coefficient is strictly positive. -/
theorem normalizedCriticalRootWeight_pos (p : (Complexify F)[X]) (hn : 0 < p.natDegree)
    (hs : p.Splits) {w : Complexify F} (hw : p.eval w ≠ 0) (a : p.roots) :
    0 < normalizedCriticalRootWeight p w a :=
  div_pos (criticalRootWeight_pos p hw a) (criticalWeightTotal_pos p hn hs hw)

/-- The normalized barycentric coefficients sum to one in `F`. -/
theorem sum_normalizedCriticalRootWeight (p : (Complexify F)[X]) (hn : 0 < p.natDegree)
    (hs : p.Splits) {w : Complexify F} (hw : p.eval w ≠ 0) :
    ∑ a : p.roots, normalizedCriticalRootWeight p w a = 1 := by
  simp only [normalizedCriticalRootWeight, div_eq_mul_inv, ← sum_mul]
  exact mul_inv_cancel₀ (criticalWeightTotal_pos p hn hs hw).ne'

/-- The normalized weighted sum of root occurrences equals the critical point. -/
theorem sum_normalizedCriticalRootWeight_smul (p : (Complexify F)[X])
    (hn : 0 < p.natDegree) (hs : p.Splits) {w : Complexify F} (hw : p.eval w ≠ 0)
    (hd : p.derivative.eval w = 0) :
    (∑ a : p.roots, normalizedCriticalRootWeight p w a • (a : Complexify F)) = w := by
  calc
    _ = (criticalWeightTotal p w)⁻¹ •
        ∑ a : p.roots, criticalRootWeight p w a • (a : Complexify F) := by
      simp only [normalizedCriticalRootWeight, div_eq_mul_inv, mul_smul, smul_sum]
      apply sum_congr rfl
      intro a _
      exact smul_comm _ _ _
    _ = w := (critical_point_eq_barycentric p hn hs hw hd).symm

/-- Gauss--Lucas in the native `F`-convex hull, including critical points
which are themselves roots of the original polynomial. -/
theorem critical_point_mem_convexHull_roots (p : (Complexify F)[X])
    (hn : 0 < p.natDegree) (hs : p.Splits) {w : Complexify F}
    (hd : p.derivative.IsRoot w) :
    w ∈ convexHull F {a : Complexify F | p.IsRoot a} := by
  by_cases hw : p.eval w = 0
  · exact subset_convexHull F _ hw
  · rw [← sum_normalizedCriticalRootWeight_smul p hn hs hw hd]
    apply (convex_convexHull F _).sum_mem
    · intro a _
      exact (normalizedCriticalRootWeight_pos p hn hs hw a).le
    · exact sum_normalizedCriticalRootWeight p hn hs hw
    · intro a _
      exact subset_convexHull F _ (isRoot_of_mem_roots Multiset.coe_mem)

/-- Set-theoretic form of the finite Gauss--Lucas theorem. -/
theorem derivative_roots_subset_convexHull (p : (Complexify F)[X])
    (hn : 0 < p.natDegree) (hs : p.Splits) :
    {w : Complexify F | p.derivative.IsRoot w} ⊆ convexHull F {a | p.IsRoot a} :=
  fun _ hw => critical_point_mem_convexHull_roots p hn hs hw

/-- Grouping occurrence weights recovers the source's multiplicity-weighted
barycentric denominator. -/
theorem criticalWeightTotal_eq_sum_multiplicities (p : (Complexify F)[X])
    (w : Complexify F) :
    criticalWeightTotal p w = ∑ a ∈ p.roots.toFinset,
      (p.rootMultiplicity a : F) / modulus (w - a) ^ 2 := by
  unfold criticalWeightTotal criticalRootWeight
  calc
    _ = (p.roots.map fun a => (modulus (w - a) ^ 2)⁻¹).sum :=
      congrArg Multiset.sum (Multiset.map_univ p.roots (fun a => (modulus (w - a) ^ 2)⁻¹))
    _ = _ := by
      rw [Finset.sum_multiset_map_count]
      simp only [Polynomial.count_roots, nsmul_eq_mul, div_eq_mul_inv]

/-- Grouping the weighted root sum retains each root's algebraic multiplicity. -/
theorem critical_weighted_root_sum_eq_sum_multiplicities (p : (Complexify F)[X])
    (w : Complexify F) :
    (∑ a : p.roots, criticalRootWeight p w a • (a : Complexify F)) =
      ∑ a ∈ p.roots.toFinset, ((p.rootMultiplicity a : F) / modulus (w - a) ^ 2) • a := by
  unfold criticalRootWeight
  calc
    _ = (p.roots.map fun a => (modulus (w - a) ^ 2)⁻¹ • a).sum :=
      congrArg Multiset.sum (Multiset.map_univ p.roots (fun a => (modulus (w - a) ^ 2)⁻¹ • a))
    _ = _ := by
      rw [Finset.sum_multiset_map_count]
      simp only [Polynomial.count_roots, div_eq_mul_inv, mul_smul, Nat.cast_smul_eq_nsmul]

/-- Every grouped weight in the displayed formula is strictly positive. -/
theorem groupedCriticalRootWeight_pos (p : (Complexify F)[X]) {w a : Complexify F}
    (hw : p.eval w ≠ 0) (ha : a ∈ p.roots) :
    0 < (p.rootMultiplicity a : F) / modulus (w - a) ^ 2 := by
  have hm : 0 < p.rootMultiplicity a := by
    rw [← Polynomial.count_roots]
    exact Multiset.count_pos.mpr ha
  have hwa : w - a ≠ 0 := by
    intro h
    exact hw ((sub_eq_zero.mp h) ▸ isRoot_of_mem_roots ha)
  exact div_pos (Nat.cast_pos.mpr hm) (pow_pos (modulus_pos hwa) 2)

/-- The displayed `polynomial:eq:barycentric`, grouped by distinct root values.
Division by the real denominator is expressed as scalar multiplication. -/
theorem critical_point_eq_barycentric_grouped (p : (Complexify F)[X])
    (hn : 0 < p.natDegree) (hs : p.Splits) {w : Complexify F} (hw : p.eval w ≠ 0)
    (hd : p.derivative.eval w = 0) :
    w = (∑ a ∈ p.roots.toFinset, (p.rootMultiplicity a : F) / modulus (w - a) ^ 2)⁻¹ •
      ∑ a ∈ p.roots.toFinset, ((p.rootMultiplicity a : F) / modulus (w - a) ^ 2) • a := by
  simpa only [criticalWeightTotal_eq_sum_multiplicities,
    critical_weighted_root_sum_eq_sum_multiplicities] using
      critical_point_eq_barycentric p hn hs hw hd

/-- The same `F`-convex hull contains the roots of a nonzero higher derivative,
provided every preceding derivative splits in the coefficient field. These
splitting hypotheses are automatic in an algebraically closed field, but are
kept explicit here. The case `k = 0` is included. -/
theorem iterate_derivative_roots_subset_convexHull (p : (Complexify F)[X]) (k : ℕ)
    (hs : ∀ j < k, ((derivative^[j]) p).Splits) (hk : (derivative^[k]) p ≠ 0) :
    {w : Complexify F | ((derivative^[k]) p).IsRoot w} ⊆
      convexHull F {a | p.IsRoot a} := by
  induction k with
  | zero => exact subset_convexHull F _
  | succ k ih =>
    have hd : derivative ((derivative^[k]) p) ≠ 0 := by
      simpa only [Function.iterate_succ_apply'] using hk
    have hn : 0 < ((derivative^[k]) p).natDegree := by
      apply Nat.pos_of_ne_zero
      intro h
      exact hd (derivative_of_natDegree_zero h)
    have hprev : (derivative^[k]) p ≠ 0 := ne_zero_of_natDegree_gt hn
    have hinc := ih (fun j hj => hs j (Nat.lt_succ_of_lt hj)) hprev
    intro w hw
    apply convexHull_min hinc (convex_convexHull F _)
    exact critical_point_mem_convexHull_roots ((derivative^[k]) p) hn
      (hs k (Nat.lt_succ_self k)) (by simpa only [Function.iterate_succ_apply', Set.mem_setOf_eq] using hw)

end Surreal.FinitePolynomial
