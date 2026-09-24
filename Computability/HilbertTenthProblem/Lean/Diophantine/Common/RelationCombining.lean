import Diophantine.Common.RelationCombiningPolynomial
import Diophantine.Common.RelationCombiningBounds
import Diophantine.Common.RelationCombiningArithmetic
import Diophantine.Common.RadicalIndependence

/-!
# The Matiyasevich--Robinson relation-combining theorem

The integer polynomial `RelationCombiningPolynomial.value` combines any finite
family of square conditions, one divisibility, and one strict positivity
condition, using a single natural witness. The divisor must be nonzero;
all radicands and the other parameters may be signed integers.

The proof uses Galois fixed fields and separated radical weights, followed
by the integer arithmetic of a vanishing factor. No relation-combining
theorem is assumed as an axiom.
-/

namespace Diophantine.RelationCombining

open RelationCombiningPolynomial RelationCombiningBounds

theorem signed_sq {S : Type*} [CommRing S] (b : Bool) (x : S) :
    signed b x ^ 2 = x ^ 2 := by
  cases b <;> simp [signed]

/-- Once integer roots are supplied, a zero value is exactly a vanishing
signed factor. -/
theorem value_zero_iff_factor {q : ℕ} (A r : Fin q → ℤ) (n B C D : ℤ)
    (hr : ∀ i, r i ^ 2 = A i) :
    value q A n B C D = 0 ↔ ∃ ε : Fin q → Bool,
      B ^ 2 * n + C ^ 2 = B ^ 2 * (2 * D - 1) *
        (C ^ 2 + weight A ^ q + ∑ i, signed (ε i) (r i) * weight A ^ i.val) := by
  have heval := value_eq_product (S := ℤ) q A n B C D r (by simpa using hr)
  simp only [Int.cast_id] at heval
  rw [heval]
  simp only [radicalProduct, weight, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero]

/-- A zero polynomial value forces all the radicands to be integer squares.
The proof permits repeated square classes and negative radicands. -/
theorem squares_of_value_zero {q : ℕ} {A : Fin q → ℤ} {n B C D : ℤ}
    (hB : B ≠ 0) (hzero : value q A n B C D = 0) :
    ∀ i, IsSquare (A i) := by
  classical
  choose r hr using fun i => RadicalField.exists_sqrt (A i)
  have hprod : radicalProduct q (fun i => (A i : RadicalField)) r n B C D = 0 := by
    rw [← value_eq_product q A n B C D r hr, hzero, Int.cast_zero]
  obtain ⟨ε, hε⟩ : ∃ ε : Fin q → Bool,
      (B : RadicalField) ^ 2 * n + (C : RadicalField) ^ 2 -
        (B : RadicalField) ^ 2 * (2 * D - 1) *
          ((C : RadicalField) ^ 2 + (weight A : RadicalField) ^ q +
            ∑ i, signed (ε i) (r i) * (weight A : RadicalField) ^ i.val) = 0 := by
    simpa only [radicalProduct, weight, Int.cast_add, Int.cast_one,
      Int.cast_sum, Int.cast_pow, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and] using hprod
  let r' : Fin q → RadicalField := fun i => signed (ε i) (r i)
  have hr' : ∀ i, r' i ^ 2 = (A i : RadicalField) := by
    intro i
    simpa only [r', signed_sq] using hr i
  obtain ⟨u, hu⟩ := RelationCombiningArithmetic.sum_rational_of_factor
    (T := weight A ^ q) (n := n) (s := ∑ i, r' i * (weight A : RadicalField) ^ i.val)
    hB (by simpa only [Int.cast_pow, r'] using hε)
  exact RadicalIndependence.isSquare_of_rational_powerSum hr' (one_le_weight A)
    (norm_root_le (fun i => RadicalField.toComplex_sq (hr' i))) hu

/-- Necessity for the complete relation-combining theorem. -/
theorem conditions_of_value_zero {q : ℕ} {A : Fin q → ℤ} {n : ℕ} {B C D : ℤ}
    (hB : B ≠ 0) (hzero : value q A n B C D = 0) :
    (∀ i, IsSquare (A i)) ∧ B ∣ C ∧ 0 < D := by
  classical
  have hsquares := squares_of_value_zero hB hzero
  have hroots : ∀ i, ∃ r : ℤ, r ^ 2 = A i := by
    intro i
    obtain ⟨r, hr⟩ := hsquares i
    exact ⟨r, by simpa only [pow_two] using hr.symm⟩
  choose r hr using hroots
  obtain ⟨ε, hε⟩ := (value_zero_iff_factor A r n B C D hr).mp hzero
  have hroot : ∀ i, signed (ε i) (r i) ^ 2 = A i := by
    intro i
    rw [signed_sq, hr i]
  exact ⟨hsquares, RelationCombiningArithmetic.conditions_of_factor hB
    (one_le_offset hroot) (by simpa only [add_assoc] using hε)⟩

/-- Sufficiency, with one new natural witness and the all-positive sign
choice relative to an arbitrary family of integer roots. -/
theorem exists_value_zero_of_conditions {q : ℕ} {A : Fin q → ℤ} {B C D : ℤ}
    (hB : B ≠ 0) (hsquares : ∀ i, IsSquare (A i)) (hdiv : B ∣ C) (hD : 0 < D) :
    ∃ n : ℕ, value q A n B C D = 0 := by
  classical
  have hroots : ∀ i, ∃ r : ℤ, r ^ 2 = A i := by
    intro i
    obtain ⟨r, hr⟩ := hsquares i
    exact ⟨r, by simpa only [pow_two] using hr.symm⟩
  choose r hr using hroots
  obtain ⟨n, hn⟩ := RelationCombiningArithmetic.exists_factor_of_conditions
    hB (one_le_offset hr) hdiv hD
  refine ⟨n, (value_zero_iff_factor A r n B C D hr).mpr ⟨fun _ => true, ?_⟩⟩
  simpa [signed, add_assoc] using hn

/-- The relation-combining theorem, with no restriction on the signs of the
radicands, dividend, or positivity parameter. The empty family is included. -/
theorem relationCombining_iff {q : ℕ} (A : Fin q → ℤ) (B C D : ℤ) (hB : B ≠ 0) :
    (∀ i, IsSquare (A i)) ∧ B ∣ C ∧ 0 < D ↔
      ∃ n : ℕ, value q A n B C D = 0 := by
  constructor
  · rintro ⟨hsquares, hdiv, hD⟩
    exact exists_value_zero_of_conditions hB hsquares hdiv hD
  · rintro ⟨n, hn⟩
    exact conditions_of_value_zero hB hn

end Diophantine.RelationCombining
