import Surreal.Algebra.SquarefreeRadicands
import Surreal.Algebra.QuadraticAdjoinCoordinates
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Finitely many squarefree square radicands in a number field

The remaining finiteness prerequisite of `odg:def:lem:tailored`. Distinct
squarefree naturals other than one give distinct quadratic intermediate
fields. Mathlib's primitive-element theorem makes the collection of all
intermediate fields finite, without requiring a chosen Galois closure.
-/

namespace Surreal.SquarefreeRadicands

variable {K : Type*} [Field K] [CharZero K]

/-- A square root of a squarefree natural other than one is irrational. -/
theorem root_irrational {n : ℕ} (hn : Squarefree n) (hn1 : n ≠ 1)
    {x : K} (hx : x ^ 2 = (n : K)) : ∀ r : ℚ, x ≠ (r : K) := by
  intro r hr
  apply hn1
  apply eq_one_of_rat_isSquare hn
  refine ⟨r, ?_⟩
  rw [hr] at hx
  have he : r ^ 2 = (n : ℚ) := by exact_mod_cast hx
  simpa only [pow_two] using he.symm

/-- Two irrational square roots of squarefree naturals in the same quadratic
simple field have the same radicand. -/
theorem eq_of_root_mem_adjoin {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hm1 : m ≠ 1) (hn1 : n ≠ 1) {x y : K} (hx : x ^ 2 = (n : K))
    (hy : y ^ 2 = (m : K)) (hmem : y ∈ IntermediateField.adjoin ℚ {x}) : m = n := by
  have hirr := root_irrational hn hn1 hx
  obtain ⟨a, b, rfl⟩ := QuadraticAdjoinCoordinates.exists_affine_of_mem_adjoin
    (n : ℚ) (by simpa only [Rat.cast_natCast] using hx) hirr hmem
  have hlin : (((a ^ 2 + b ^ 2 * (n : ℚ) - m : ℚ) : K)) +
      ((2 * a * b : ℚ) : K) * x = 0 := by
    push_cast
    linear_combination hy - (b : K) ^ 2 * hx
  obtain ⟨hc, hab⟩ := QuadraticAdjoinCoordinates.affine_eq_zero hirr
    (a ^ 2 + b ^ 2 * (n : ℚ) - m) (2 * a * b) hlin
  have hab' : a = 0 ∨ b = 0 := by
    rcases mul_eq_zero.mp hab with ha | hb
    · exact Or.inl ((mul_eq_zero.mp ha).resolve_left (by norm_num))
    · exact Or.inr hb
  rcases hab' with ha | hb
  · apply eq_of_rat_square_factor hm hn b
    rw [ha] at hc
    nlinarith [hc]
  · exfalso
    apply hm1
    apply eq_one_of_rat_isSquare hm
    refine ⟨a, ?_⟩
    rw [hb] at hc
    nlinarith [hc]

/-- A number field contains square roots of only finitely many squarefree natural radicands. -/
theorem numberField_finite (K : Type*) [Field K] [NumberField K] :
    Set.Finite {n : ℕ | Squarefree n ∧ IsSquare (n : K)} := by
  classical
  letI : Finite (IntermediateField ℚ K) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ K
      (Field.exists_primitive_element ℚ K)
  let S : Set ℕ := {n | Squarefree n ∧ n ≠ 1 ∧ IsSquare (n : K)}
  let root (n : S) : K := n.property.2.2.choose
  have root_sq (n : S) : root n ^ 2 = (n.val : K) := by
    simpa only [pow_two] using n.property.2.2.choose_spec.symm
  let f (n : S) : IntermediateField ℚ K := IntermediateField.adjoin ℚ {root n}
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply eq_of_root_mem_adjoin a.property.1 b.property.1 a.property.2.1 b.property.2.1
      (root_sq b) (root_sq a)
    change root a ∈ f b
    rw [← he]
    exact IntermediateField.mem_adjoin_simple_self ℚ (root a)
  letI : Finite S := Finite.of_injective f hf
  have hS : S.Finite := Set.toFinite S
  apply (hS.insert 1).subset
  intro n hn
  by_cases hn1 : n = 1
  · exact Or.inl hn1
  · exact Or.inr ⟨hn.1, hn1, hn.2⟩

end Surreal.SquarefreeRadicands
