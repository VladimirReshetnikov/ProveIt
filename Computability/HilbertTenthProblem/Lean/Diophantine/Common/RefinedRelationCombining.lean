import Diophantine.Common.RefinedRelationCombiningPolynomial
import Diophantine.Common.RefinedRelationCombiningArithmetic
import Diophantine.Common.RefinedRelationCombiningBounds
import Diophantine.Common.RelationCombining

/-!
# Relation combining with separate radical weights

The refined ordinary integer polynomial combines square conditions,
divisibility, and strict positivity using one natural witness. Each radicand
has its own integer weight bounding every complex square root with one unit
of room. The unsquared divisibility parameters require a positive divisor
and a nonnegative dividend.

The square tests may involve negative integers or repeated square classes.
Their necessity follows from the proved rationality criterion for separated
radical sums; no independence of square classes is assumed.
-/

namespace Diophantine.RefinedRelationCombining

open RefinedRelationCombiningPolynomial RefinedRelationCombiningBounds
open RelationCombiningPolynomial (signed)
open RelationCombining (signed_sq)

private theorem cast_prefix {q : ℕ} {S : Type*} [CommRing S]
    (V : Fin q → ℤ) (m : ℕ) :
    ((weightPrefix V m : ℤ) : S) = weightPrefix (fun i => (V i : S)) m :=
  map_prefix (Int.castRingHom S) V m

/-- Integer roots inherit the given complex-root bounds. -/
theorem abs_root_le {q : ℕ} {A V r : Fin q → ℤ}
    (hbound : ∀ (i : Fin q) (z : ℂ), z ^ 2 = (A i : ℂ) →
      ‖z‖ ≤ (V i : ℝ) - 1)
    (hr : ∀ i, r i ^ 2 = A i) (i : Fin q) : |r i| ≤ V i - 1 := by
  have hrC : (r i : ℂ) ^ 2 = (A i : ℂ) := by exact_mod_cast hr i
  have h := hbound i (r i : ℂ) hrC
  simp only [Complex.norm_intCast] at h
  exact_mod_cast h

/-- Given integer roots, a vanishing polynomial value is exactly a
vanishing signed factor. -/
theorem value_zero_iff_factor {q : ℕ} (A V r : Fin q → ℤ) (n B C D : ℤ)
    (hr : ∀ i, r i ^ 2 = A i) :
    value q A V n B C D = 0 ↔ ∃ ε : Fin q → Bool,
      B * n + C = B * (2 * D - 1) *
        (C + weightPrefix V q + ∑ i, signed (ε i) (r i) * weightPrefix V i.val) := by
  have heval := value_eq_product (S := ℤ) q A V n B C D r (by simpa using hr)
  simp only [Int.cast_id] at heval
  rw [heval]
  simp only [radicalProduct, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero]

/-- A zero value forces every radicand to be an integer square. Only the
nonzero divisor and the radical-weight bounds are needed at this stage. -/
theorem squares_of_value_zero {q : ℕ} {A V : Fin q → ℤ} {n B C D : ℤ}
    (hv : ∀ i, 1 ≤ V i)
    (hbound : ∀ (i : Fin q) (z : ℂ), z ^ 2 = (A i : ℂ) →
      ‖z‖ ≤ (V i : ℝ) - 1)
    (hB : B ≠ 0) (hzero : value q A V n B C D = 0) :
    ∀ i, IsSquare (A i) := by
  classical
  choose r hr using fun i => RadicalField.exists_sqrt (A i)
  have hprod : radicalProduct q (fun i => (V i : RadicalField)) r n B C D = 0 := by
    rw [← value_eq_product q A V n B C D r hr, hzero, Int.cast_zero]
  obtain ⟨ε, hε⟩ : ∃ ε : Fin q → Bool,
      (B : RadicalField) * n + (C : RadicalField) -
        (B : RadicalField) * (2 * D - 1) *
          ((C : RadicalField) + ((weightPrefix V q : ℤ) : RadicalField) +
            ∑ i, signed (ε i) (r i) * ((weightPrefix V i.val : ℤ) : RadicalField)) = 0 := by
    simpa only [radicalProduct, ← cast_prefix, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and] using hprod
  let r' : Fin q → RadicalField := fun i => signed (ε i) (r i)
  have hr' : ∀ i, r' i ^ 2 = (A i : RadicalField) := by
    intro i
    simpa only [r', signed_sq] using hr i
  obtain ⟨u, hu⟩ := RefinedRelationCombiningArithmetic.sum_rational_of_factor
    (T := weightPrefix V q) (n := n)
    (s := ∑ i, r' i * ((weightPrefix V i.val : ℤ) : RadicalField))
    hB (by simpa only [r'] using hε)
  exact isSquare_of_rational_prefixSum hr' hv
    (fun i => hbound i _ (RadicalField.toComplex_sq (hr' i))) hu

/-- Necessity for the refined relation-combining theorem. -/
theorem conditions_of_value_zero {q : ℕ} {A V : Fin q → ℤ} {n : ℕ} {B C D : ℤ}
    (hv : ∀ i, 1 ≤ V i)
    (hbound : ∀ (i : Fin q) (z : ℂ), z ^ 2 = (A i : ℂ) →
      ‖z‖ ≤ (V i : ℝ) - 1)
    (hB : 0 < B) (hC : 0 ≤ C) (hzero : value q A V n B C D = 0) :
    (∀ i, IsSquare (A i)) ∧ B ∣ C ∧ 0 < D := by
  classical
  have hsquares := squares_of_value_zero hv hbound (ne_of_gt hB) hzero
  have hroots : ∀ i, ∃ r : ℤ, r ^ 2 = A i := by
    intro i
    obtain ⟨r, hr⟩ := hsquares i
    exact ⟨r, by simpa only [pow_two] using hr.symm⟩
  choose r hr using hroots
  obtain ⟨ε, hε⟩ := (value_zero_iff_factor A V r n B C D hr).mp hzero
  have hroot : ∀ i, signed (ε i) (r i) ^ 2 = A i := by
    intro i
    rw [signed_sq, hr i]
  have hoffset := one_le_offset hv (abs_root_le hbound hroot)
  exact ⟨hsquares, RefinedRelationCombiningArithmetic.conditions_of_factor hB hC
    hoffset (by simpa only [add_assoc] using hε)⟩

/-- Sufficiency with precisely one additional natural witness. -/
theorem exists_value_zero_of_conditions {q : ℕ} {A V : Fin q → ℤ} {B C D : ℤ}
    (hv : ∀ i, 1 ≤ V i)
    (hbound : ∀ (i : Fin q) (z : ℂ), z ^ 2 = (A i : ℂ) →
      ‖z‖ ≤ (V i : ℝ) - 1)
    (hB : 0 < B) (hC : 0 ≤ C)
    (hsquares : ∀ i, IsSquare (A i)) (hdiv : B ∣ C) (hD : 0 < D) :
    ∃ n : ℕ, value q A V n B C D = 0 := by
  classical
  have hroots : ∀ i, ∃ r : ℤ, r ^ 2 = A i := by
    intro i
    obtain ⟨r, hr⟩ := hsquares i
    exact ⟨r, by simpa only [pow_two] using hr.symm⟩
  choose r hr using hroots
  obtain ⟨n, hn⟩ := RefinedRelationCombiningArithmetic.exists_factor_of_conditions
    hB hC (one_le_offset hv (abs_root_le hbound hr)) hdiv hD
  refine ⟨n, (value_zero_iff_factor A V r n B C D hr).mpr ⟨fun _ => true, ?_⟩⟩
  simpa [signed, add_assoc] using hn

/-- Refined relation combining, allowing signed radicands and including
the empty family of square tests. -/
theorem relationCombining_iff {q : ℕ} (A V : Fin q → ℤ) (B C D : ℤ)
    (hv : ∀ i, 1 ≤ V i)
    (hbound : ∀ (i : Fin q) (z : ℂ), z ^ 2 = (A i : ℂ) →
      ‖z‖ ≤ (V i : ℝ) - 1)
    (hB : 0 < B) (hC : 0 ≤ C) :
    (∀ i, IsSquare (A i)) ∧ B ∣ C ∧ 0 < D ↔
      ∃ n : ℕ, value q A V n B C D = 0 := by
  constructor
  · rintro ⟨hsquares, hdiv, hD⟩
    exact exists_value_zero_of_conditions hv hbound hB hC hsquares hdiv hD
  · rintro ⟨n, hn⟩
    exact conditions_of_value_zero hv hbound hB hC hn

end Diophantine.RefinedRelationCombining
