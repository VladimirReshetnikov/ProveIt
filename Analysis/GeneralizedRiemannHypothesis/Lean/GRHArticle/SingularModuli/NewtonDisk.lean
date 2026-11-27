import GRHArticle.SingularModuli.NewtonRoots
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.Padics.Complex

/-!
# Newton's strict-disk count in the original coordinate

An affine substitution moves the disk to the origin. Separability identifies
the count with the cardinality of the corresponding set of distinct roots.
-/

namespace GRHArticle.SingularModuli

open Polynomial
open scoped Classical Ring

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- For a unit-norm center parameter, the transformed root norm is the
relative distance from the original center. -/
theorem isLeastMaximalCoeff_affine_disk (H : Polynomial K) (hH : H ≠ 0)
    (hs : H.Splits) (a u : K) (ha : a ≠ 0) (hu : ‖u‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    IsLeastMaximalCoeff (H.comp (C a * (C u + X))) r
      (H.roots.filter (fun x => ‖x / (a * u) - 1‖ < r)).card := by
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  rw [mul_add, ← C_mul, add_comm (C (a * u))]
  have hA : (C a * X + C (a * u)).natDegree = 1 := by
    rw [natDegree_add_C, natDegree_C_mul_X a ha]
  have h0 : H.comp (C a * X + C (a * u)) ≠ 0 := by
    intro hc
    rcases comp_eq_zero_iff.mp hc with h | ⟨_, h⟩
    · exact hH h
    · have hd := congrArg Polynomial.natDegree h
      simp only [hA, natDegree_C] at hd
      omega
  have h := isLeastMaximalCoeff_card_roots h0 (hs.comp_of_natDegree_le_one hA.le) hr
  rw [roots_comp_C_mul_X_add_C H a (a * u) ha.isUnit, Multiset.filter_map, Multiset.card_map] at h
  have hn (x : K) : ‖a⁻¹ʳ * (x - a * u)‖ = ‖x / (a * u) - 1‖ := by
    have he : a⁻¹ʳ * (x - a * u) = (x / (a * u) - 1) * u := by
      rw [Ring.inverse_eq_inv]
      field_simp [ha, hu0]
    rw [he, norm_mul, hu, mul_one]
  simpa only [Function.comp_apply, hn] using h

/-- Exact cardinality of the distinct roots in the affine strict disk. -/
theorem eq_ncard_affine_disk_of_isLeastMaximalCoeff {H : Polynomial K} (hH : H ≠ 0)
    (hs : H.Splits) (hsep : H.Separable) {a u : K} (ha : a ≠ 0) (hu : ‖u‖ = 1)
    {r : ℝ} (hr : 0 < r) {i : ℕ}
    (hi : IsLeastMaximalCoeff (H.comp (C a * (C u + X))) r i) :
    i = {x : K | H.eval x = 0 ∧ ‖x / (a * u) - 1‖ < r}.ncard := by
  let s := H.roots.filter (fun x => ‖x / (a * u) - 1‖ < r)
  have hnodup : s.Nodup := (Polynomial.nodup_roots hsep).filter _
  have hset : (s.toFinset : Set K) = {x : K | H.eval x = 0 ∧ ‖x / (a * u) - 1‖ < r} := by
    ext x
    simp [s, Polynomial.mem_roots hH, Polynomial.IsRoot, and_comm]
  rw [← hset, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup hnodup]
  exact hi.unique (isLeastMaximalCoeff_affine_disk H hH hs a u ha hu hr)

/-- The strict-disk count of smd:lem:newton in the equivalent norm form
with center p^v * u and radius p^(-λ). -/
theorem padic_eq_ncard_strict_disk_of_isLeastMaximalCoeff
    {p : ℕ} [hp : Fact p.Prime] {H : Polynomial ℂ_[p]} (hH : H ≠ 0)
    (hsep : H.Separable) (v : ℕ) (u : ℤ) (hu : IsCoprime u (p : ℤ))
    (depth : ℚ) {i : ℕ}
    (hi : IsLeastMaximalCoeff (H.comp (C ((p : ℂ_[p]) ^ v) * (C (u : ℂ_[p]) + X)))
      ((p : ℝ) ^ (-(depth : ℝ))) i) :
    i = {x : ℂ_[p] | H.eval x = 0 ∧
      ‖x / ((p : ℂ_[p]) ^ v * (u : ℂ_[p])) - 1‖ < (p : ℝ) ^ (-(depth : ℝ))}.ncard := by
  have ha : (p : ℂ_[p]) ^ v ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hR : 0 < (p : ℝ) ^ (-(depth : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have hu' : ‖(u : ℂ_[p])‖ = 1 := by
    rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) u]
    exact (PadicComplex.norm_extends' p _).trans (Padic.norm_intCast_eq_one_iff.mpr hu)
  exact eq_ncard_affine_disk_of_isLeastMaximalCoeff hH (IsAlgClosed.splits H) hsep ha hu' hR hi

end GRHArticle.SingularModuli
