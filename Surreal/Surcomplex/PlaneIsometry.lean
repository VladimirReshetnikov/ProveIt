import Surreal.Surcomplex.Modulus
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Affine isometries of the actual surcomplex plane

Translations, multiplication by unit directions and conjugation preserve
the actual surreal-valued distance. Every pair of distinct points can be
sent to zero and its positive real distance by an affine equivalence over
the actual surreal field. These constructions supply the Euclidean
congruence maps in `trigonometry:thm:sss` without a real-valued metric.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- An affine equivalence preserves the actual surreal-valued distances. -/
def PreservesModulus (f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u}) : Prop :=
  ∀ z w, modulus (f z - f w) = modulus (z - w)

namespace PreservesModulus

theorem refl : PreservesModulus (AffineEquiv.refl SignSequence.{u} Surcomplex.{u}) := by
  intro z w
  rfl

/-- Composing two affine isometries preserves all actual distances. -/
theorem trans {f g : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u}}
    (hf : PreservesModulus f) (hg : PreservesModulus g) : PreservesModulus (f.trans g) := by
  intro z w
  exact (hg (f z) (f w)).trans (hf z w)

/-- The inverse of an affine isometry preserves all actual distances. -/
theorem symm {f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u}}
    (hf : PreservesModulus f) : PreservesModulus f.symm := by
  intro z w
  simpa only [AffineEquiv.apply_symm_apply] using (hf (f.symm z) (f.symm w)).symm

end PreservesModulus

/-- Translation by an arbitrary actual surcomplex vector as a Mathlib affine equivalence. -/
def translationAffineEquiv (a : Surcomplex.{u}) :
    Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u} :=
  AffineEquiv.constVAdd SignSequence Surcomplex a

@[simp] theorem translationAffineEquiv_apply (a z : Surcomplex.{u}) :
    translationAffineEquiv a z = a + z := rfl

theorem preservesModulus_translation (a : Surcomplex.{u}) :
    PreservesModulus (translationAffineEquiv a) := by
  intro z w
  simp only [translationAffineEquiv_apply, add_sub_add_left_eq_sub]

/-- Multiplication by a nonzero surcomplex number, with its real-linear and affine structures. -/
def mulAffineEquiv (a : Surcomplex.{u}ˣ) :
    Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u} :=
  (Units.mulLeftLinearEquiv SignSequence Surcomplex a).toAffineEquiv

@[simp] theorem mulAffineEquiv_apply (a : Surcomplex.{u}ˣ) (z : Surcomplex.{u}) :
    mulAffineEquiv a z = (a : Surcomplex.{u}) * z := rfl

/-- Multiplication scales every actual distance by the multiplier's actual modulus. -/
theorem modulus_mulAffineEquiv_sub (a : Surcomplex.{u}ˣ) (z w : Surcomplex.{u}) :
    modulus (mulAffineEquiv a z - mulAffineEquiv a w) =
      modulus (a : Surcomplex.{u}) * modulus (z - w) := by
  rw [mulAffineEquiv_apply, mulAffineEquiv_apply, ← mul_sub, modulus_mul]

theorem preservesModulus_mul (a : Surcomplex.{u}ˣ) (ha : modulus (a : Surcomplex.{u}) = 1) :
    PreservesModulus (mulAffineEquiv a) := by
  intro z w
  rw [modulus_mulAffineEquiv_sub, ha, one_mul]

/-- Conjugation is linear over the actual surreal scalars. -/
def conjLinearEquiv : Surcomplex.{u} ≃ₗ[SignSequence.{u}] Surcomplex.{u} where
  toEquiv := conj.toEquiv
  map_add' := conj.map_add
  map_smul' r z := by
    change conj (r • z) = r • conj z
    rw [Algebra.smul_def, Algebra.smul_def]
    change conj (ofReal r * z) = ofReal r * conj z
    rw [map_mul, conj_ofReal]

/-- Reflection in the real axis as an affine equivalence. -/
def conjAffineEquiv : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u} :=
  conjLinearEquiv.toAffineEquiv

@[simp] theorem conjAffineEquiv_apply (z : Surcomplex.{u}) : conjAffineEquiv z = conj z := rfl

theorem preservesModulus_conj : PreservesModulus (conjAffineEquiv :
    Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u}) := by
  intro z w
  rw [conjAffineEquiv_apply, conjAffineEquiv_apply, ← map_sub, modulus_conj]

/-- The conjugate of a nonzero vector's normalized direction has unit modulus. -/
theorem modulus_conj_div_modulus (z : Surcomplex.{u}) (hz : z ≠ 0) :
    modulus (conj z / ofReal (modulus z)) = 1 := by
  rw [modulus_div, modulus_conj, modulus_ofReal, abs_of_nonneg (modulus_nonneg z),
    div_self (modulus_pos hz).ne']

/-- Multiplication by the conjugate normalized direction places the vector on the positive axis. -/
theorem conj_div_modulus_mul (z : Surcomplex.{u}) (hz : z ≠ 0) :
    (conj z / ofReal (modulus z)) * z = ofReal (modulus z) := by
  have hr : ofReal (modulus z) ≠ 0 :=
    (map_ne_zero ofReal).mpr (modulus_pos hz).ne'
  calc
    _ = (z * conj z) / ofReal (modulus z) := by ring
    _ = ofReal (normSq z) / ofReal (modulus z) := by rw [mul_conj]
    _ = _ := by
      apply (div_eq_iff hr).mpr
      rw [← map_mul, ← pow_two, modulus_sq]

/-- Any distinct pair can be placed at zero and its positive actual distance by an isometry. -/
theorem exists_normalizing_affineEquiv (A B : Surcomplex.{u}) (h : A ≠ B) :
    ∃ f : Surcomplex.{u} ≃ᵃ[SignSequence.{u}] Surcomplex.{u},
      f A = 0 ∧ f B = ofReal (modulus (B - A)) ∧ PreservesModulus f := by
  have hz : B - A ≠ 0 := sub_ne_zero.mpr h.symm
  have hm := modulus_conj_div_modulus (B - A) hz
  have hu : conj (B - A) / ofReal (modulus (B - A)) ≠ 0 := by
    intro he
    rw [he, modulus_zero] at hm
    exact zero_ne_one hm
  let a : Surcomplex.{u}ˣ := Units.mk0 _ hu
  refine ⟨(translationAffineEquiv (-A)).trans (mulAffineEquiv a), ?_, ?_, ?_⟩
  · simp only [AffineEquiv.trans_apply, translationAffineEquiv_apply,
      mulAffineEquiv_apply, neg_add_cancel, mul_zero]
  · change (conj (B - A) / ofReal (modulus (B - A))) * (-A + B) = _
    rw [show -A + B = B - A by abel]
    exact conj_div_modulus_mul (B - A) hz
  · exact (preservesModulus_translation (-A)).trans (preservesModulus_mul a hm)

end
end Surreal.Surcomplex
