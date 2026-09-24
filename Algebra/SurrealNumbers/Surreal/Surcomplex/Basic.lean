import Surreal.Foundations.SignSequenceField
import Surreal.Algebra.Complexify

/-!
# Surcomplex numbers over the constructed surreal field

The actual ordinal-sign field now supplies the base of the quadratic pair
construction in `found:sub:pairs`. This specializes `found:eq:pairadd`, `found:eq:pairmul`,
`found:eq:conj`, `found:eq:pairinv`, and the field assertion of
`found:prop:complex`. The field instance is inherited from the existing
quadratic-algebra construction, using the proved order on the sign field.

No real-closedness, algebraic-closedness, square-root or modulus statement is
asserted here. Norm squares are valued in the sign field itself.
-/

universe u

namespace Surreal

/-- Surcomplex numbers are quadratic pairs over the constructed sign field,
with the relation `i² = -1`. The carrier is in `Type (u + 1)`. -/
abbrev Surcomplex : Type (u + 1) := Complexify Foundations.SignSequence.{u}

namespace Surcomplex

open Foundations

noncomputable section

-- Reuse the generic field instance; no competing instance is introduced.
example : Field Surcomplex.{u} := inferInstance

/-- Embed a surreal sign sequence on the real axis. -/
def ofReal : SignSequence.{u} →+* Surcomplex.{u} :=
  algebraMap SignSequence.{u} Surcomplex.{u}

@[simp] theorem ofReal_re (a : SignSequence.{u}) : (ofReal a).re = a := rfl
@[simp] theorem ofReal_im (a : SignSequence.{u}) : (ofReal a).im = 0 := rfl

theorem ofReal_injective : Function.Injective (ofReal : SignSequence.{u} → Surcomplex.{u}) :=
  QuadraticAlgebra.algebraMap_injective

/-- Equality is precisely coordinatewise equality. -/
@[ext] theorem ext {z w : Surcomplex.{u}} (hre : z.re = w.re) (him : z.im = w.im) : z = w :=
  QuadraticAlgebra.ext hre him

/-- The imaginary unit in `found:eq:conj`. -/
def I : Surcomplex.{u} := Complexify.I

@[simp] theorem I_re : (I : Surcomplex.{u}).re = 0 := rfl
@[simp] theorem I_im : (I : Surcomplex.{u}).im = 1 := rfl

@[simp] theorem I_sq : (I : Surcomplex.{u}) ^ 2 = -1 := Complexify.I_sq

/-- The concrete coordinate pair form of `found:eq:pairadd`. -/
theorem add_eq (z w : Surcomplex.{u}) :
    z + w = ⟨z.re + w.re, z.im + w.im⟩ := rfl

/-- The real component of the actual multiplication (`found:eq:pairmul`). -/
@[simp] theorem mul_re (z w : Surcomplex.{u}) :
    (z * w).re = z.re * w.re - z.im * w.im := Complexify.mul_re z w

/-- The imaginary component of the actual multiplication (`found:eq:pairmul`). -/
@[simp] theorem mul_im (z w : Surcomplex.{u}) :
    (z * w).im = z.re * w.im + z.im * w.re := Complexify.mul_im z w

/-- The concrete coordinate pair form of `found:eq:pairmul`. -/
theorem mul_eq (z w : Surcomplex.{u}) :
    z * w = ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ :=
  QuadraticAlgebra.ext (mul_re z w) (mul_im z w)

/-- Conjugation as an automorphism of the concrete surcomplex field. -/
def conj : Surcomplex.{u} ≃+* Surcomplex.{u} := starRingAut

@[simp] theorem conj_re (z : Surcomplex.{u}) : (conj z).re = z.re := Complexify.conj_re z
@[simp] theorem conj_im (z : Surcomplex.{u}) : (conj z).im = -z.im := Complexify.conj_im z

/-- The coordinate pair formula `found:eq:conj`. -/
theorem conj_eq (z : Surcomplex.{u}) : conj z = ⟨z.re, -z.im⟩ := by
  ext <;> simp

@[simp] theorem conj_conj (z : Surcomplex.{u}) : conj (conj z) = z := Complexify.conj_conj z

theorem conj_mul (z w : Surcomplex.{u}) : conj (z * w) = conj z * conj w := conj.map_mul z w

@[simp] theorem conj_ofReal (a : SignSequence.{u}) : conj (ofReal a) = ofReal a := by
  ext <;> simp

@[simp] theorem conj_I : conj (I : Surcomplex.{u}) = -I := by
  ext <;> simp

/-- Every surcomplex has its real-plus-imaginary coordinate decomposition. -/
theorem re_add_im_mul_I (z : Surcomplex.{u}) :
    ofReal z.re + ofReal z.im * I = z := by
  ext <;> simp

/-- The surreal-valued norm square; no square root is required. -/
def normSq (z : Surcomplex.{u}) : SignSequence.{u} := Complexify.normSq z

theorem normSq_eq (z : Surcomplex.{u}) : normSq z = z.re ^ 2 + z.im ^ 2 := rfl

theorem normSq_nonneg (z : Surcomplex.{u}) : 0 ≤ normSq z := Complexify.normSq_nonneg z

@[simp] theorem normSq_eq_zero_iff (z : Surcomplex.{u}) : normSq z = 0 ↔ z = 0 :=
  Complexify.normSq_eq_zero_iff z

/-- The denominator in `found:eq:pairinv` is positive for a nonzero pair. -/
theorem normSq_pos {z : Surcomplex.{u}} (hz : z ≠ 0) : 0 < normSq z :=
  Complexify.normSq_pos hz

theorem normSq_mul (z w : Surcomplex.{u}) : normSq (z * w) = normSq z * normSq w :=
  Complexify.normSq_mul z w

theorem mul_conj (z : Surcomplex.{u}) : z * conj z = ofReal (normSq z) :=
  Complexify.mul_conj z

/-- `found:eq:pairinv`, including Lean's total inverse convention at zero. -/
@[simp] theorem inv_re (z : Surcomplex.{u}) : (z⁻¹).re = z.re / normSq z :=
  Complexify.inv_re z

@[simp] theorem inv_im (z : Surcomplex.{u}) : (z⁻¹).im = -z.im / normSq z :=
  Complexify.inv_im z

/-- The concrete coordinate pair form of `found:eq:pairinv`. -/
theorem inv_eq (z : Surcomplex.{u}) : z⁻¹ = ⟨z.re / normSq z, -z.im / normSq z⟩ := by
  exact QuadraticAlgebra.ext (inv_re z) (inv_im z)

/-- Surcomplexification has dimension two over the constructed surreal field. -/
theorem finrank_eq_two : Module.finrank SignSequence.{u} Surcomplex.{u} = 2 :=
  QuadraticAlgebra.finrank_eq_two (-1) 0

/-- The surcomplex carrier cannot fit in the universe of sign birthdays:
its real embedding already contains the entire sign carrier. -/
theorem not_small : ¬ Small.{u} Surcomplex.{u} := by
  intro h
  letI := h
  exact SignSequence.not_small (small_of_injective ofReal_injective)

end

end Surcomplex

end Surreal
