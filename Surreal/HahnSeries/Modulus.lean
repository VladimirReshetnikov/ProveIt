import Surreal.Algebra.Modulus
import Surreal.Algebra.RealClosedReal
import Surreal.HahnSeries.RealClosed
import Surreal.HahnSeries.ExponentialConjugation

/-!
# A real-Hahn-valued modulus for complex Hahn series

Complex Hahn series are identified with the quadratic extension of the
lexicographically ordered real Hahn field. Its constructed nonnegative square
roots give a modulus with values in that real Hahn field. The unit-circle
condition is exactly `z * conjugate z = 1`, so the infinitesimal logarithm of
a near-one series of modulus one has purely imaginary coefficients.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Transport each real coordinate to the lexicographic order synonym. -/
def complexifyHahnToLexEquiv : Complexify (ℝ⟦Γ⟧) ≃+* Complexify (Lex ℝ⟦Γ⟧) where
  toFun z := ⟨hahnToLexRingEquiv z.re, hahnToLexRingEquiv z.im⟩
  invFun z := ⟨hahnToLexRingEquiv.symm z.re, hahnToLexRingEquiv.symm z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem complexifyHahnToLexEquiv_conj (z : Complexify (ℝ⟦Γ⟧)) :
    complexifyHahnToLexEquiv (star z) = star (complexifyHahnToLexEquiv z) := by
  apply QuadraticAlgebra.ext <;> simp [complexifyHahnToLexEquiv]

/-- Complex Hahn series as the quadratic extension of the ordered real Hahn field. -/
def complexHahnLexEquiv : ℂ⟦Γ⟧ ≃+* Complexify (Lex ℝ⟦Γ⟧) :=
  realComplexHahnEquiv.symm.trans complexifyHahnToLexEquiv

@[simp] theorem complexHahnLexEquiv_conjugation (z : ℂ⟦Γ⟧) :
    complexHahnLexEquiv (complexConjugation z) = star (complexHahnLexEquiv z) := by
  obtain ⟨w, rfl⟩ := realComplexHahnEquiv.surjective z
  simp [complexHahnLexEquiv]

variable [DivisibleBy Γ ℕ]

/-- The modulus takes its values in the ordered real Hahn field, rather than
collapsing infinite or infinitesimal scales to ordinary real numbers. -/
def complexModulus (z : ℂ⟦Γ⟧) : Lex ℝ⟦Γ⟧ :=
  Complexify.modulus (complexHahnLexEquiv z)

theorem complexModulus_nonneg (z : ℂ⟦Γ⟧) : 0 ≤ complexModulus z :=
  Complexify.modulus_nonneg _

theorem complexModulus_sq (z : ℂ⟦Γ⟧) :
    complexModulus z ^ 2 = Complexify.normSq (complexHahnLexEquiv z) :=
  Complexify.modulus_sq _

@[simp] theorem complexModulus_zero : complexModulus (0 : ℂ⟦Γ⟧) = 0 := by
  simp [complexModulus]

@[simp] theorem complexModulus_one : complexModulus (1 : ℂ⟦Γ⟧) = 1 := by
  simp [complexModulus]

@[simp] theorem complexModulus_eq_zero_iff (z : ℂ⟦Γ⟧) :
    complexModulus z = 0 ↔ z = 0 := by
  simp [complexModulus]

theorem complexModulus_pos {z : ℂ⟦Γ⟧} (hz : z ≠ 0) : 0 < complexModulus z :=
  lt_of_le_of_ne (complexModulus_nonneg z)
    (Ne.symm (mt (complexModulus_eq_zero_iff z).mp hz))

@[simp] theorem complexModulus_conjugation (z : ℂ⟦Γ⟧) :
    complexModulus (complexConjugation z) = complexModulus z := by
  simp [complexModulus]

@[simp] theorem complexModulus_neg (z : ℂ⟦Γ⟧) :
    complexModulus (-z) = complexModulus z := by
  simp [complexModulus]

theorem complexModulus_mul (z w : ℂ⟦Γ⟧) :
    complexModulus (z * w) = complexModulus z * complexModulus w := by
  simp only [complexModulus, map_mul, Complexify.modulus_mul]

theorem complexModulus_add_le (z w : ℂ⟦Γ⟧) :
    complexModulus (z + w) ≤ complexModulus z + complexModulus w := by
  simpa only [complexModulus, map_add] using
    Complexify.modulus_add_le (complexHahnLexEquiv z) (complexHahnLexEquiv w)

/-- The literal modulus-one condition is the algebraic unit-circle condition. -/
theorem complexModulus_eq_one_iff (z : ℂ⟦Γ⟧) :
    complexModulus z = 1 ↔ z * complexConjugation z = 1 := by
  constructor
  · intro h
    apply complexHahnLexEquiv.injective
    rw [map_mul, complexHahnLexEquiv_conjugation, Complexify.mul_conj, map_one,
      ← complexModulus_sq, h, one_pow, map_one]
  · intro h
    apply Complexify.modulus_eq_of_nonneg_sq zero_le_one
    have h' := congrArg (fun w : ℂ⟦Γ⟧ => (complexHahnLexEquiv w).re) h
    simp only [map_mul, complexHahnLexEquiv_conjugation, Complexify.mul_conj,
      map_one, QuadraticAlgebra.re_one] at h'
    change Complexify.normSq (complexHahnLexEquiv z) = 1 at h'
    simpa only [one_pow] using h'.symm

/-- Conjugation negates the infinitesimal logarithm of a near-one series
whose real-Hahn-valued modulus is one. -/
theorem complexConjugation_infLog_eq_neg_of_modulus_eq_one (z : ℂ⟦Γ⟧)
    (hz : 0 < (z - 1).orderTop) (hmod : complexModulus z = 1) :
    complexConjugation (infLog (z - 1) hz) = -infLog (z - 1) hz :=
  complexConjugation_infLog_eq_neg_of_mul_conj_eq_one z hz
    ((complexModulus_eq_one_iff z).mp hmod)

/-- The literal modulus-one hypothesis in `e:prop-infexp` implies that
every coefficient of the near-one logarithm is purely imaginary. -/
theorem infLog_re_eq_zero_of_modulus_eq_one (z : ℂ⟦Γ⟧)
    (hz : 0 < (z - 1).orderTop) (hmod : complexModulus z = 1) (g : Γ) :
    ((infLog (z - 1) hz).coeff g).re = 0 :=
  infLog_re_eq_zero_of_mul_conj_eq_one z hz ((complexModulus_eq_one_iff z).mp hmod) g

end
end Surreal.HahnSeries
