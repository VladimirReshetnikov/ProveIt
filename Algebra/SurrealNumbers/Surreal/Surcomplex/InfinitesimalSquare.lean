import Surreal.Surcomplex.AlgebraicallyClosed
import Surreal.Surcomplex.Leading
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Infinitesimal square roots in the actual surcomplex field

The square-root change of variable in `trigonometry:thm:fold` stays in the
infinitesimal monad. This follows from the actual surreal-valued modulus,
including arbitrary complex arguments and the zero case. The square-root
valuation is exact at every nonzero scale. Coordinatewise closure and
conjugation criteria also support the real and purely imaginary branches.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Zero belongs to the actual infinitesimal monad. -/
theorem infinitesimal_zero : IsInfinitesimal (0 : Surcomplex.{u}) :=
  ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩

/-- The actual infinitesimal monad is closed under addition. -/
theorem infinitesimal_add {x y : Surcomplex.{u}}
    (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) : IsInfinitesimal (x + y) :=
  ⟨SignSequence.infinitesimal_add hx.1 hy.1, SignSequence.infinitesimal_add hx.2 hy.2⟩

/-- Negating an actual infinitesimal preserves infinitesimality. -/
theorem infinitesimal_neg {x : Surcomplex.{u}} (hx : IsInfinitesimal x) :
    IsInfinitesimal (-x) :=
  ⟨SignSequence.infinitesimal_neg hx.1, SignSequence.infinitesimal_neg hx.2⟩

/-- An actual infinitesimal times a finite surcomplex is infinitesimal. -/
theorem infinitesimal_mul_finite {x y : Surcomplex.{u}}
    (hx : IsInfinitesimal x) (hy : IsFinite y) : IsInfinitesimal (x * y) := by
  constructor
  · rw [mul_re]
    rw [sub_eq_add_neg]
    exact SignSequence.infinitesimal_add
      (SignSequence.infinitesimal_mul_finite hx.1 hy.1)
      (SignSequence.infinitesimal_neg (SignSequence.infinitesimal_mul_finite hx.2 hy.2))
  · rw [mul_im]
    exact SignSequence.infinitesimal_add
      (SignSequence.infinitesimal_mul_finite hx.1 hy.2)
      (SignSequence.infinitesimal_mul_finite hx.2 hy.1)

/-- A finite surcomplex times an actual infinitesimal is infinitesimal. -/
theorem finite_mul_infinitesimal {x y : Surcomplex.{u}}
    (hx : IsFinite x) (hy : IsInfinitesimal y) : IsInfinitesimal (x * y) := by
  simpa only [mul_comm] using infinitesimal_mul_finite hy hx

/-- Ordinary complex scalar multiplication preserves actual infinitesimals. -/
theorem infinitesimal_ofComplex_mul (r : ℂ) {x : Surcomplex.{u}}
    (hx : IsInfinitesimal x) : IsInfinitesimal (ofComplex r * x) :=
  finite_mul_infinitesimal (finite_ofComplex r) hx

/-- The product of two actual infinitesimals is infinitesimal. -/
theorem infinitesimal_mul {x y : Surcomplex.{u}}
    (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) : IsInfinitesimal (x * y) :=
  infinitesimal_mul_finite hx (finite_of_infinitesimal hy)

/-- Squaring detects actual complex infinitesimality without any restriction
on the direction, or any prior finiteness assumption. -/
theorem infinitesimal_sq_iff (z : Surcomplex.{u}) :
    IsInfinitesimal (z ^ 2) ↔ IsInfinitesimal z := by
  rw [isInfinitesimal_iff_modulus, isInfinitesimal_iff_modulus]
  have hm : modulus (z ^ 2) = modulus z ^ 2 := modulusMonoidWithZeroHom.map_pow z 2
  rw [hm, SignSequence.infinitesimal_sq_iff]

/-- Every chosen square root of an infinitesimal is infinitesimal. -/
theorem infinitesimal_of_sq_eq {z τ : Surcomplex.{u}} (hs : z ^ 2 = τ)
    (hτ : IsInfinitesimal τ) : IsInfinitesimal z :=
  (infinitesimal_sq_iff z).mp (hs.symm ▸ hτ)

/-- The square relation preserves and reflects membership in the monad. -/
theorem infinitesimal_iff_of_sq_eq {z τ : Surcomplex.{u}} (hs : z ^ 2 = τ) :
    IsInfinitesimal z ↔ IsInfinitesimal τ := by
  rw [← hs, infinitesimal_sq_iff]

/-- Algebraic closedness supplies a square root inside the infinitesimal
monad itself, with no choice of complex branch required. -/
theorem exists_infinitesimal_sq_eq (τ : Surcomplex.{u}) (hτ : IsInfinitesimal τ) :
    ∃ z : Surcomplex.{u}, IsInfinitesimal z ∧ z ^ 2 = τ := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq τ (by decide : 0 < (2 : ℕ))
  exact ⟨z, infinitesimal_of_sq_eq hz hτ, hz⟩

/-- The intrinsic half-valuation relation includes the zero case. -/
theorem two_nsmul_valuation_of_sq_eq {z τ : Surcomplex.{u}} (hs : z ^ 2 = τ) :
    2 • valuation z = valuation τ := by
  rw [← hs, valuation.map_pow]

/-- A square root has precisely half the finite valuation exponent of
its nonzero square, at arbitrary actual surcomplex scales. -/
theorem valuation_of_sq_eq {z τ : Surcomplex.{u}} (hs : z ^ 2 = τ) (hτ : τ ≠ 0) :
    valuation z = ((-leadingExponent τ / 2 : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  have hm : modulus z ^ 2 = modulus τ := by
    calc
      modulus z ^ 2 = modulus (z ^ 2) := (modulusMonoidWithZeroHom.map_pow z 2).symm
      _ = modulus τ := congrArg modulus hs
  have hr := SignSequence.sqrt_eq_of_nonneg_sq (modulus_nonneg z) hm
  rw [valuation_eq_modulus, ← hr, SignSequence.valuation_sqrt (modulus_pos hτ)]
  rfl

/-- Conjugation fixes exactly the actual real axis. -/
theorem conj_eq_self_iff_im_eq_zero (z : Surcomplex.{u}) : conj z = z ↔ z.im = 0 := by
  constructor
  · intro h
    have hi := congrArg (fun w : Surcomplex.{u} => w.im) h
    simp only [conj_im] at hi
    linarith
  · intro h
    apply ext
    · simp
    · simp [h]

/-- Conjugation negates exactly the actual purely imaginary axis. -/
theorem conj_eq_neg_iff_re_eq_zero (z : Surcomplex.{u}) : conj z = -z ↔ z.re = 0 := by
  constructor
  · intro h
    have hr := congrArg (fun w : Surcomplex.{u} => w.re) h
    simp only [conj_re, QuadraticAlgebra.re_neg] at hr
    linarith
  · intro h
    apply ext
    · simpa only [conj_re, QuadraticAlgebra.re_neg] using (show z.re = -z.re by rw [h, neg_zero])
    · rfl

end

end Surreal.Surcomplex
