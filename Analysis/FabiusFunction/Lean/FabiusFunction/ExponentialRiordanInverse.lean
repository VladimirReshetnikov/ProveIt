import FabiusFunction.ExponentialRiordan

/-!
# Construction of the two-sided inverse of an exponential Riordan array

Let `g` have invertible constant coefficient, and let `f` have zero constant coefficient
and invertible linear coefficient.  Write `f̄` for Mathlib's constructed compositional
inverse of `f`.  The inverse array is `[h, f̄]`, where `h = (1/g) ∘ f̄`.

The weight `h` is constructed over an arbitrary commutative ring.  Its two defining
identities, `g * h(f) = 1` and `h * g(f̄) = 1`, then give both array products over a
commutative `ℚ`-algebra by the existing conditional Riordan inverse law.  Thus neither
an inverse series nor an inverse prefactor is assumed as additional data.
-/

set_option autoImplicit false

open scoped BigOperators
open PowerSeries

namespace Fabius

section CommRing

variable {R : Type*} [CommRing R]

/-- The constructed weight `(1/g) ∘ f̄` of the inverse Riordan array, using the scalar
unit of `g` to construct its multiplicative inverse and the linear unit of `f` to
construct its compositional inverse. -/
noncomputable def riordanInverseWeight (g f : R⟦X⟧)
    (hg : IsUnit (constantCoeff g)) (hf1 : IsUnit (coeff 1 f)) : R⟦X⟧ :=
  (invOfUnit g hg.unit).subst (f.substInvOfIsUnit hf1)

/-- The inverse weight is a multiplicative inverse of `g ∘ f̄`, over any commutative
ring.  This identity needs only that the constructed `f̄` has zero constant term. -/
theorem riordanInverseWeight_mul_subst (g f : R⟦X⟧)
    (hg : IsUnit (constantCoeff g)) (hf1 : IsUnit (coeff 1 f)) :
    riordanInverseWeight g f hg hf1 * g.subst (f.substInvOfIsUnit hf1) = 1 := by
  have hs : HasSubst (f.substInvOfIsUnit hf1) := HasSubst.substInvOfIsUnit f hf1
  rw [riordanInverseWeight, ← subst_mul hs, invOfUnit_mul g hg.unit hg.unit_spec.symm,
    ← coe_substAlgHom hs, map_one]

/-- Substitution by `f` sends the inverse weight back to `1/g`.  Consequently the
weights in the forward Riordan product cancel, over any commutative ring. -/
theorem mul_riordanInverseWeight_subst (g f : R⟦X⟧)
    (hg : IsUnit (constantCoeff g)) (hf0 : constantCoeff f = 0)
    (hf1 : IsUnit (coeff 1 f)) :
    g * (riordanInverseWeight g f hg hf1).subst f = 1 := by
  have hs : HasSubst f := HasSubst.of_constantCoeff_zero' hf0
  have hsi : HasSubst (f.substInvOfIsUnit hf1) := HasSubst.substInvOfIsUnit f hf1
  rw [riordanInverseWeight, subst_comp_subst_apply hsi hs,
    subst_substInvOfIsUnit_left f hf0 hf1, X_subst,
    mul_invOfUnit g hg.unit hg.unit_spec.symm]

end CommRing

section RatAlgebra

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The array constructed from the inverse weight and the compositional inverse is a
right inverse of `[g,f]`, entrywise with the finite lower-triangular product. -/
theorem expRiordan_mul_constructedInverse (g f : R⟦X⟧)
    (hg : IsUnit (constantCoeff g)) (hf0 : constantCoeff f = 0)
    (hf1 : IsUnit (coeff 1 f)) (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1), expRiordan R g f n j *
      expRiordan R (riordanInverseWeight g f hg hf1) (f.substInvOfIsUnit hf1) j k =
        if n = k then 1 else 0 :=
  expRiordan_mul_inverse R hf0 (constantCoeff_substInvOfIsUnit f hf1)
    (subst_substInvOfIsUnit_left f hf0 hf1) g (riordanInverseWeight g f hg hf1)
    (mul_riordanInverseWeight_subst g f hg hf0 hf1) n k

/-- The same constructed array is a left inverse of `[g,f]`; no additional inverse
series or prefactor hypothesis is needed. -/
theorem expRiordan_constructedInverse_mul (g f : R⟦X⟧)
    (hg : IsUnit (constantCoeff g)) (hf0 : constantCoeff f = 0)
    (hf1 : IsUnit (coeff 1 f)) (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
      expRiordan R (riordanInverseWeight g f hg hf1) (f.substInvOfIsUnit hf1) n j *
        expRiordan R g f j k = if n = k then 1 else 0 :=
  expRiordan_mul_inverse R (constantCoeff_substInvOfIsUnit f hf1) hf0
    (subst_substInvOfIsUnit_right f hf0 hf1) (riordanInverseWeight g f hg hf1) g
    (riordanInverseWeight_mul_subst g f hg hf1) n k

end RatAlgebra

end Fabius
