import Surreal.Surcomplex.ExpLogConjugation
import Surreal.Surcomplex.FiniteExponential

/-!
# Finite-angle polar representations

The actual finite exponential supplies polar representations of every
nonzero surcomplex, with finite real surreal angles. Two finite angles
give the same phase exactly when their difference is an ordinary integral
multiple of `2π`. This proves the polar existence and ambiguity clauses
of `e:prop-polar`, without defining trigonometric functions at infinite angles.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private theorem finite_conj {z : Surcomplex.{u}} (hz : IsFinite z) : IsFinite (conj z) := by
  constructor
  · simpa only [conj_re] using hz.1
  · simpa only [conj_im] using SignSequence.finite_neg hz.2

/-- Conjugation restricts to the actual finite subring. -/
def finiteConj : finiteSubring.{u} ≃+* finiteSubring.{u} where
  toFun z := ⟨conj z.val, finite_conj z.property⟩
  invFun z := ⟨conj z.val, finite_conj z.property⟩
  left_inv z := by apply Subtype.ext; exact conj_conj z.val
  right_inv z := by apply Subtype.ext; exact conj_conj z.val
  map_mul' z w := by apply Subtype.ext; exact map_mul conj z.val w.val
  map_add' z w := by apply Subtype.ext; exact map_add conj z.val w.val

@[simp] theorem coe_finiteConj (z : finiteSubring.{u}) :
    (finiteConj z : Surcomplex.{u}) = conj (z : Surcomplex.{u}) := rfl

/-- Multiply a finite real angle by the imaginary unit, retaining its finite domain. -/
def finiteImaginary : SignSequence.FiniteElement.{u} →+ finiteSubring.{u} where
  toFun θ := ⟨ofReal θ.val * I, by
    constructor
    · simp only [mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero, zero_mul, sub_zero]
      exact SignSequence.finite_zero
    · simp only [mul_im, ofReal_re, I_re, ofReal_im, I_im, mul_one, zero_mul, add_zero]
      exact θ.property⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' θ φ := by
    apply Subtype.ext
    change ofReal (θ.val + φ.val) * I = ofReal θ.val * I + ofReal φ.val * I
    rw [map_add, add_mul]

@[simp] theorem coe_finiteImaginary (θ : SignSequence.FiniteElement.{u}) :
    (finiteImaginary θ : Surcomplex.{u}) = ofReal θ.val * I := rfl

/-- The imaginary embedding is faithful on finite angles. -/
theorem finiteImaginary_injective : Function.Injective (finiteImaginary.{u}) := by
  intro θ φ h
  apply ArchimedeanClass.FiniteElement.ext
  have him := congrArg (fun z : finiteSubring.{u} => (z : Surcomplex.{u}).im) h
  simpa using him

private theorem imaginary_period_eq (n : ℤ) :
    ofReal (SignSequence.ofReal ((n : ℝ) * (2 * Real.pi))) * I =
      (ofComplex ((n : ℂ) * (2 * Real.pi * Complex.I)) : Surcomplex.{u}) := by
  rw [← ofComplex_ofReal, ← ofComplex_I, ← map_mul]
  congr 1
  push_cast
  ring

/-- The ordinary complex period is precisely the imaginary image of the real period. -/
theorem finiteImaginary_eq_period_iff (θ : SignSequence.FiniteElement.{u}) (n : ℤ) :
    (finiteImaginary θ : Surcomplex.{u}) = ofComplex ((n : ℂ) * (2 * Real.pi * Complex.I)) ↔
      θ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi)) := by
  rw [← imaginary_period_eq, coe_finiteImaginary]
  constructor
  · intro h
    simpa using congrArg (fun z : Surcomplex.{u} => z.im) h
  · intro h
    rw [h]

/-- Finite exponentiation commutes with conjugation on its explicit finite domain. -/
theorem finiteExp_conj (z : finiteSubring.{u}) :
    finiteExp (finiteConj z) = conj (finiteExp z) := by
  have hc : standardPartHom (finiteConj z) = star (standardPartHom z) :=
    standardPart_conj z.val
  have hp : (infinitesimalPart (finiteConj z)).val = conj (infinitesimalPart z).val := by
    simp only [coe_infinitesimalPart, hc, coe_finiteConj, ofComplex_conj, map_sub]
  have he : Complex.exp (star (standardPartHom z)) = star (Complex.exp (standardPartHom z)) :=
    Complex.exp_conj _
  rw [finiteExp, finiteExp, map_mul, hc, he, ofComplex_conj]
  congr 1
  simpa only [hp] using infExp_conj (infinitesimalPart z).val (infinitesimalPart z).property

/-- A finite real angle has a phase given by the finite exponential of its imaginary image. -/
def finitePhase (θ : SignSequence.FiniteElement.{u}) : Surcomplex.{u} :=
  finiteExp (finiteImaginary θ)

/-- The complete period ambiguity for finite angles. -/
theorem finitePhase_eq_iff (θ φ : SignSequence.FiniteElement.{u}) :
    finitePhase θ = finitePhase φ ↔ ∃ n : ℤ,
      θ.val - φ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi)) := by
  rw [finitePhase, finitePhase, finiteExp_eq_finiteExp_iff]
  apply exists_congr
  intro n
  change ((finiteImaginary θ - finiteImaginary φ : finiteSubring.{u}) : Surcomplex.{u}) = _ ↔ _
  rw [← map_sub]
  exact finiteImaginary_eq_period_iff (θ - φ) n

private theorem finiteConj_finiteImaginary (θ : SignSequence.FiniteElement.{u}) :
    finiteConj (finiteImaginary θ) = -finiteImaginary θ := by
  apply Subtype.ext
  change conj (ofReal θ.val * I) = -(ofReal θ.val * I)
  rw [map_mul, conj_ofReal, conj_I, mul_neg]

/-- Every finite phase lies on the actual unit circle. -/
theorem modulus_finitePhase (θ : SignSequence.FiniteElement.{u}) :
    modulus (finitePhase θ) = 1 := by
  have hc : conj (finitePhase θ) = (finitePhase θ)⁻¹ := by
    rw [finitePhase, ← finiteExp_conj, finiteConj_finiteImaginary, finiteExp_neg]
  have hprod : finitePhase θ * conj (finitePhase θ) = 1 := by
    rw [hc]
    exact mul_inv_cancel₀ (finiteExp_ne_zero _)
  have hs := congrArg (fun z : Surcomplex.{u} => z.re) hprod
  rw [mul_conj, ofReal_re, ← modulus_sq] at hs
  change modulus (finitePhase θ) ^ 2 = 1 at hs
  have hn := modulus_nonneg (finitePhase θ)
  nlinarith

/-- Every actual unit-circle point is the phase of a finite real angle. -/
theorem exists_finitePhase_eq_of_modulus_eq_one (z : Surcomplex.{u}) (hz : modulus z = 1) :
    ∃ θ : SignSequence.FiniteElement.{u}, finitePhase θ = z := by
  have hfinite : IsFinite z := (isFinite_iff_modulus z).mpr (hz ▸ SignSequence.finite_one)
  have hc : standardPart z ≠ 0 := by
    intro hc
    have hm := standardPart_modulus hfinite
    rw [hz, SignSequence.standardPart_one, hc, norm_zero] at hm
    exact one_ne_zero hm
  obtain ⟨w, hw⟩ := exists_finiteExp_eq ⟨z, hfinite⟩ hc
  have hsum : finiteExp (w + finiteConj w) = 1 := by
    rw [finiteExp_add, finiteExp_conj, hw, mul_conj, ← modulus_sq, hz, one_pow, map_one]
  obtain ⟨n, hn⟩ := (finiteExp_eq_one_iff (w + finiteConj w)).mp hsum
  have hre : (w : Surcomplex.{u}).re = 0 := by
    have h := congrArg (fun z : Surcomplex.{u} => z.re) hn
    have h' : (w : Surcomplex.{u}).re + (w : Surcomplex.{u}).re = 0 := by
      simpa [Complex.mul_re, Complex.mul_im] using h
    linarith
  let θ : SignSequence.FiniteElement.{u} := ⟨(w : Surcomplex.{u}).im, w.property.2⟩
  refine ⟨θ, ?_⟩
  have he : finiteImaginary θ = w := by
    apply Subtype.ext
    change ofReal (w : Surcomplex.{u}).im * I = (w : Surcomplex.{u})
    have h := re_add_im_mul_I (w : Surcomplex.{u})
    simpa only [hre, map_zero, zero_add] using h
  rw [finitePhase, he, hw]

/-- Every nonzero surcomplex has a polar representation with a finite real angle. -/
theorem exists_polar (z : Surcomplex.{u}) (hz : z ≠ 0) :
    ∃ θ : SignSequence.FiniteElement.{u}, z = ofReal (modulus z) * finitePhase θ := by
  have hr : modulus z ≠ 0 := (modulus_eq_zero_iff z).not.mpr hz
  let w := z / ofReal (modulus z)
  have hw : modulus w = 1 := by
    rw [modulus_div, modulus_ofReal, abs_of_nonneg (modulus_nonneg z), div_self hr]
  obtain ⟨θ, hθ⟩ := exists_finitePhase_eq_of_modulus_eq_one w hw
  refine ⟨θ, ?_⟩
  rw [hθ]
  dsimp only [w]
  have hr' : ofReal (modulus z) ≠ 0 := (map_ne_zero ofReal).mpr hr
  field_simp

/-- With the prescribed positive modulus, exactly the ordinary periods identify two angles. -/
theorem polar_angle_eq_iff (z : Surcomplex.{u}) (hz : z ≠ 0)
    (θ φ : SignSequence.FiniteElement.{u}) :
    ofReal (modulus z) * finitePhase θ = ofReal (modulus z) * finitePhase φ ↔
      ∃ n : ℤ, θ.val - φ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi)) := by
  rw [mul_right_inj' ((map_ne_zero ofReal).mpr ((modulus_eq_zero_iff z).not.mpr hz)),
    finitePhase_eq_iff]

end

end Surreal.Surcomplex
