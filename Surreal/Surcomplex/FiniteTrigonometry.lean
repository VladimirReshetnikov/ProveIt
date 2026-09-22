import Surreal.Surcomplex.Polar

/-!
# Algebra of finite surreal angles

Sine and cosine are the imaginary and real coordinates of the actual finite
phase. They agree with ordinary sine and cosine on real constants and obey
the algebraic identities in `trigonometry:thm:identities`, including integer
de Moivre. The domain remains the finite real surreal subring.

This file does not identify these coordinates with the separate even and odd
Taylor sums in `trigonometry:eq:sinfinite` and `trigonometry:eq:cosfinite`,
and makes no differentiability or infinite-angle assertion.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Cosine of a finite real surreal angle, defined by the actual finite phase. -/
def finiteCos (θ : SignSequence.FiniteElement.{u}) : SignSequence.{u} :=
  (finitePhase θ).re

/-- Sine of a finite real surreal angle, defined by the actual finite phase. -/
def finiteSin (θ : SignSequence.FiniteElement.{u}) : SignSequence.{u} :=
  (finitePhase θ).im

/-- Euler's coordinate identity for finite angles. -/
theorem finitePhase_eq_cos_add_sin_mul_I (θ : SignSequence.FiniteElement.{u}) :
    finitePhase θ = ofReal (finiteCos θ) + ofReal (finiteSin θ) * I :=
  (re_add_im_mul_I (finitePhase θ)).symm

@[simp] theorem finitePhase_zero : finitePhase (0 : SignSequence.FiniteElement.{u}) = 1 := by
  rw [finitePhase, map_zero, finiteExp_zero]

/-- Addition of finite angles multiplies their phases. -/
theorem finitePhase_add (θ φ : SignSequence.FiniteElement.{u}) :
    finitePhase (θ + φ) = finitePhase θ * finitePhase φ := by
  rw [finitePhase, map_add, finiteExp_add]
  rfl

/-- Negating a finite angle inverts its phase. -/
theorem finitePhase_neg (θ : SignSequence.FiniteElement.{u}) :
    finitePhase (-θ) = (finitePhase θ)⁻¹ := by
  rw [finitePhase, map_neg, finiteExp_neg]
  rfl

/-- Negating a finite angle also conjugates its phase. -/
theorem finitePhase_neg_eq_conj (θ : SignSequence.FiniteElement.{u}) :
    finitePhase (-θ) = conj (finitePhase θ) := by
  have h : finiteConj (finiteImaginary θ) = finiteImaginary (-θ) := by
    apply Subtype.ext
    change conj (ofReal θ.val * I) = ofReal (-θ.val) * I
    rw [map_mul, conj_ofReal, conj_I, map_neg]
    ring
  rw [finitePhase, ← h, finiteExp_conj]
  rfl

theorem finitePhase_sub (θ φ : SignSequence.FiniteElement.{u}) :
    finitePhase (θ - φ) = finitePhase θ / finitePhase φ := by
  rw [sub_eq_add_neg, finitePhase_add, finitePhase_neg, div_eq_mul_inv]

/-- The finite phase retains its ordinary complex value at real constants. -/
@[simp] theorem finitePhase_constant (r : ℝ) :
    finitePhase (SignSequence.finiteOfReal r : SignSequence.FiniteElement.{u}) =
      ofComplex (Complex.exp ((r : ℂ) * Complex.I)) := by
  have h : finiteImaginary (SignSequence.finiteOfReal r) =
      (⟨ofComplex ((r : ℂ) * Complex.I), finite_ofComplex _⟩ : finiteSubring.{u}) := by
    apply Subtype.ext
    change ofReal (SignSequence.ofReal r) * I = ofComplex ((r : ℂ) * Complex.I)
    rw [map_mul, ofComplex_ofReal, ofComplex_I]
  rw [finitePhase, h, finiteExp_constant]

@[simp] theorem finiteCos_constant (r : ℝ) :
    finiteCos (SignSequence.finiteOfReal r : SignSequence.FiniteElement.{u}) =
      SignSequence.ofReal (Real.cos r) := by
  simp only [finiteCos, finitePhase_constant, ofComplex_re, Complex.exp_ofReal_mul_I_re]

@[simp] theorem finiteSin_constant (r : ℝ) :
    finiteSin (SignSequence.finiteOfReal r : SignSequence.FiniteElement.{u}) =
      SignSequence.ofReal (Real.sin r) := by
  simp only [finiteSin, finitePhase_constant, ofComplex_im, Complex.exp_ofReal_mul_I_im]

@[simp] theorem finiteCos_zero : finiteCos (0 : SignSequence.FiniteElement.{u}) = 1 := by
  simp [finiteCos, QuadraticAlgebra.re_one]

@[simp] theorem finiteSin_zero : finiteSin (0 : SignSequence.FiniteElement.{u}) = 0 := by
  simp [finiteSin, QuadraticAlgebra.im_one]

/-- The cosine addition formula on the explicit finite domain. -/
theorem finiteCos_add (θ φ : SignSequence.FiniteElement.{u}) :
    finiteCos (θ + φ) = finiteCos θ * finiteCos φ - finiteSin θ * finiteSin φ := by
  simpa only [finiteCos, finiteSin, mul_re] using
    congrArg (fun z : Surcomplex.{u} => z.re) (finitePhase_add θ φ)

/-- The sine addition formula on the explicit finite domain. -/
theorem finiteSin_add (θ φ : SignSequence.FiniteElement.{u}) :
    finiteSin (θ + φ) = finiteSin θ * finiteCos φ + finiteCos θ * finiteSin φ := by
  simpa only [finiteSin, finiteCos, mul_im, add_comm] using
    congrArg (fun z : Surcomplex.{u} => z.im) (finitePhase_add θ φ)

@[simp] theorem finiteCos_neg (θ : SignSequence.FiniteElement.{u}) :
    finiteCos (-θ) = finiteCos θ := by
  simp only [finiteCos, finitePhase_neg_eq_conj, conj_re]

@[simp] theorem finiteSin_neg (θ : SignSequence.FiniteElement.{u}) :
    finiteSin (-θ) = -finiteSin θ := by
  simp only [finiteSin, finitePhase_neg_eq_conj, conj_im]

theorem finiteCos_sub (θ φ : SignSequence.FiniteElement.{u}) :
    finiteCos (θ - φ) = finiteCos θ * finiteCos φ + finiteSin θ * finiteSin φ := by
  rw [sub_eq_add_neg, finiteCos_add, finiteCos_neg, finiteSin_neg, mul_neg, sub_neg_eq_add]

theorem finiteSin_sub (θ φ : SignSequence.FiniteElement.{u}) :
    finiteSin (θ - φ) = finiteSin θ * finiteCos φ - finiteCos θ * finiteSin φ := by
  rw [sub_eq_add_neg, finiteSin_add, finiteCos_neg, finiteSin_neg, mul_neg, ← sub_eq_add_neg]

/-- The unit-modulus phase gives the Pythagorean identity. -/
theorem finiteCos_sq_add_finiteSin_sq (θ : SignSequence.FiniteElement.{u}) :
    finiteCos θ ^ 2 + finiteSin θ ^ 2 = 1 := by
  have h := modulus_sq (finitePhase θ)
  rw [modulus_finitePhase, one_pow] at h
  exact h.symm

theorem isFinite_finiteCos (θ : SignSequence.FiniteElement.{u}) :
    SignSequence.IsFinite (finiteCos θ) := (isFinite_finiteExp (finiteImaginary θ)).1

theorem isFinite_finiteSin (θ : SignSequence.FiniteElement.{u}) :
    SignSequence.IsFinite (finiteSin θ) := (isFinite_finiteExp (finiteImaginary θ)).2

/-- A full ordinary turn does not change a finite phase. -/
theorem finitePhase_add_two_pi (θ : SignSequence.FiniteElement.{u}) :
    finitePhase (θ + SignSequence.finiteOfReal (2 * Real.pi)) = finitePhase θ := by
  apply (finitePhase_eq_iff _ _).mpr
  refine ⟨1, ?_⟩
  change θ.val + SignSequence.ofReal (2 * Real.pi) - θ.val = _
  simp only [Int.cast_one, one_mul, add_sub_cancel_left]

theorem finiteCos_add_two_pi (θ : SignSequence.FiniteElement.{u}) :
    finiteCos (θ + SignSequence.finiteOfReal (2 * Real.pi)) = finiteCos θ :=
  congrArg (fun z : Surcomplex.{u} => z.re) (finitePhase_add_two_pi θ)

theorem finiteSin_add_two_pi (θ : SignSequence.FiniteElement.{u}) :
    finiteSin (θ + SignSequence.finiteOfReal (2 * Real.pi)) = finiteSin θ :=
  congrArg (fun z : Surcomplex.{u} => z.im) (finitePhase_add_two_pi θ)

theorem finiteCos_periodic :
    Function.Periodic finiteCos (SignSequence.finiteOfReal (2 * Real.pi) :
      SignSequence.FiniteElement.{u}) := finiteCos_add_two_pi

theorem finiteSin_periodic :
    Function.Periodic finiteSin (SignSequence.finiteOfReal (2 * Real.pi) :
      SignSequence.FiniteElement.{u}) := finiteSin_add_two_pi

/-- Natural multiples of a finite angle give powers of the phase. -/
theorem finitePhase_nsmul (n : ℕ) (θ : SignSequence.FiniteElement.{u}) :
    finitePhase (n • θ) = finitePhase θ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, finitePhase_add, ih, pow_succ]

/-- Integer de Moivre, including negative powers. -/
theorem finitePhase_zsmul (n : ℤ) (θ : SignSequence.FiniteElement.{u}) :
    finitePhase (n • θ) = finitePhase θ ^ n := by
  cases n with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, natCast_zsmul, zpow_natCast] using finitePhase_nsmul n θ
  | negSucc n =>
    rw [negSucc_zsmul, finitePhase_neg, finitePhase_nsmul, zpow_negSucc]

/-- The coordinate form of integer de Moivre. -/
theorem finiteCos_add_finiteSin_mul_I_zpow (n : ℤ) (θ : SignSequence.FiniteElement.{u}) :
    (ofReal (finiteCos θ) + ofReal (finiteSin θ) * I) ^ n =
      ofReal (finiteCos (n • θ)) + ofReal (finiteSin (n • θ)) * I := by
  rw [← finitePhase_eq_cos_add_sin_mul_I, ← finitePhase_eq_cos_add_sin_mul_I,
    finitePhase_zsmul]

theorem finiteCos_two_mul (θ : SignSequence.FiniteElement.{u}) :
    finiteCos (2 * θ) = finiteCos θ ^ 2 - finiteSin θ ^ 2 := by
  rw [two_mul, finiteCos_add, pow_two, pow_two]

theorem finiteSin_two_mul (θ : SignSequence.FiniteElement.{u}) :
    finiteSin (2 * θ) = 2 * finiteSin θ * finiteCos θ := by
  rw [two_mul, finiteSin_add]
  ring

/-- Standard part of the imaginary angle is the ordinary imaginary angle. -/
@[simp] theorem standardPart_finiteImaginary (θ : SignSequence.FiniteElement.{u}) :
    standardPartHom (finiteImaginary θ) =
      (SignSequence.standardPartHom θ : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [standardPartHom_apply, standardPart, coe_finiteImaginary,
      SignSequence.standardPartHom_apply]

/-- The complex infinitesimal remainder is exactly `i` times the real remainder. -/
theorem infinitesimalPart_finiteImaginary (θ : SignSequence.FiniteElement.{u}) :
    (infinitesimalPart (finiteImaginary θ)).val =
      ofReal (θ.val - SignSequence.ofReal (SignSequence.standardPartHom θ)) * I := by
  rw [coe_infinitesimalPart, standardPart_finiteImaginary, coe_finiteImaginary,
    map_mul, ofComplex_ofReal, ofComplex_I, map_sub, sub_mul]

theorem infinitesimal_imaginary_angleRemainder (θ : SignSequence.FiniteElement.{u}) :
    IsInfinitesimal
      (ofReal (θ.val - SignSequence.ofReal (SignSequence.standardPartHom θ)) * I) := by
  rw [← infinitesimalPart_finiteImaginary]
  exact (infinitesimalPart (finiteImaginary θ)).property

/-- Finite Euler in ordinary-part times infinitesimal-exponential form. -/
theorem finitePhase_eq_exp_mul_infExp (θ : SignSequence.FiniteElement.{u}) :
    finitePhase θ =
      ofComplex (Complex.exp ((SignSequence.standardPartHom θ : ℂ) * Complex.I)) *
        infExp (ofReal (θ.val - SignSequence.ofReal (SignSequence.standardPartHom θ)) * I)
          (infinitesimal_imaginary_angleRemainder θ) := by
  simp only [finitePhase, finiteExp, standardPart_finiteImaginary,
    infinitesimalPart_finiteImaginary]

/-- The exponential series in finite Euler is an actual Hahn strong sum. -/
theorem finitePhase_eq_exp_mul_strongSum (θ : SignSequence.FiniteElement.{u}) :
    let η := ofReal (θ.val - SignSequence.ofReal (SignSequence.standardPartHom θ)) * I
    finitePhase θ =
      ofComplex (Complex.exp ((SignSequence.standardPartHom θ : ℂ) * Complex.I)) *
        strongSum (fun n : ℕ => ofComplex (algebraMap ℚ ℂ (1 / (n.factorial : ℚ))) * η ^ n)
          (stronglySummable_infExp η (infinitesimal_imaginary_angleRemainder θ)) := by
  dsimp only
  rw [finitePhase_eq_exp_mul_infExp, infExp_eq_strongSum]

@[simp] theorem standardPart_finiteCos (θ : SignSequence.FiniteElement.{u}) :
    SignSequence.standardPart (finiteCos θ) = Real.cos (SignSequence.standardPartHom θ) := by
  have h := congrArg Complex.re (standardPart_finiteExp (finiteImaginary θ))
  simpa only [finiteCos, finitePhase, standardPart_re, standardPart_finiteImaginary,
    Complex.exp_ofReal_mul_I_re] using h

@[simp] theorem standardPart_finiteSin (θ : SignSequence.FiniteElement.{u}) :
    SignSequence.standardPart (finiteSin θ) = Real.sin (SignSequence.standardPartHom θ) := by
  have h := congrArg Complex.im (standardPart_finiteExp (finiteImaginary θ))
  simpa only [finiteSin, finitePhase, standardPart_im, standardPart_finiteImaginary,
    Complex.exp_ofReal_mul_I_im] using h

end

end Surreal.Surcomplex
