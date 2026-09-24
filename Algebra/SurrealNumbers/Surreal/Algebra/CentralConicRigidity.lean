import Surreal.Algebra.BinaryQuadraticFactors

/-!
# Translation to the center of a nonsingular conic

Generic algebra for `odg:cor:conics`. The two center equations remove the
linear terms. A nonzero centered level and nonzero discriminant then
force constant coordinates in any constant-field algebra whose units are constants.
-/

namespace Surreal.CentralConic

noncomputable section

/-- The general affine binary quadratic, with all six coefficients explicit. -/
def value {R : Type*} [CommRing R] (a b c d e f x y : R) : R :=
  a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f

/-- Evaluation of a conic commutes with coefficient homomorphisms. -/
theorem map_value {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b c d e f x y : R) :
    φ (value a b c d e f x y) = value (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ x) (φ y) := by
  simp only [value, map_add, map_mul, map_pow]

/-- Translating by a center leaves only the homogeneous quadratic and the value at the center. -/
theorem translation {R : Type*} [CommRing R] (a b c d e f h k x y : R)
    (hh : 2 * a * h + b * k + d = 0) (hk : b * h + 2 * c * k + e = 0) :
    value a b c d e f x y =
      a * (x - h) ^ 2 + b * (x - h) * (y - k) + c * (y - k) ^ 2 +
        value a b c d e f h k := by
  unfold value
  linear_combination (x - h) * hh + (y - k) * hk

/-- The manuscript's translation identity is equivalent to the two linear center equations. -/
theorem center_iff {R : Type*} [CommRing R] (a b c d e f h k : R) :
    (∀ u v : R, value a b c d e f (h + u) (k + v) =
      a * u ^ 2 + b * u * v + c * v ^ 2 + value a b c d e f h k) ↔
      2 * a * h + b * k + d = 0 ∧ b * h + 2 * c * k + e = 0 := by
  constructor
  · intro hc
    have hx := hc 1 0
    have hy := hc 0 1
    unfold value at hx hy
    constructor
    · linear_combination hx
    · linear_combination hy
  · rintro ⟨hh, hk⟩ u v
    simpa only [add_sub_cancel_left] using translation a b c d e f h k (h + u) (k + v) hh hk

/-- Nonsingular conics with nonzero centered value have constant coordinates. -/
theorem coordinates_constant {K B : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    [CommRing B] [Algebra K B] (ct : B →ₐ[K] K)
    (hunit : ∀ z : B, IsUnit z → z = algebraMap K B (ct z))
    (a b c d e f h k : K) (hd : b ^ 2 - 4 * a * c ≠ 0)
    (hh : 2 * a * h + b * k + d = 0) (hk : b * h + 2 * c * k + e = 0)
    (hl : value a b c d e f h k ≠ 0) (x y : B)
    (he : value (algebraMap K B a) (algebraMap K B b) (algebraMap K B c)
      (algebraMap K B d) (algebraMap K B e) (algebraMap K B f) x y = 0) :
    x = algebraMap K B (ct x) ∧ y = algebraMap K B (ct y) := by
  let φ := algebraMap K B
  have hh' : 2 * φ a * φ h + φ b * φ k + φ d = 0 := by
    simpa only [map_add, map_mul, map_ofNat, map_zero] using congrArg φ hh
  have hk' : φ b * φ h + 2 * φ c * φ k + φ e = 0 := by
    simpa only [map_add, map_mul, map_ofNat, map_zero] using congrArg φ hk
  have ht := translation (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) (φ h) (φ k) x y hh' hk'
  let v : Fin 2 → B := ![x - φ h, y - φ k]
  have hv : (BinaryFormRigidity.binaryQuadratic a b c).eval₂ φ v =
      φ (-value a b c d e f h k) := by
    simp only [BinaryFormRigidity.binaryQuadratic, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_X, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, map_neg, map_value]
    linear_combination he - ht
  have hc := BinaryFormRigidity.coordinates_constant ct hunit _
    (BinaryFormRigidity.binaryQuadratic_hasTwoProjectiveFactors a b c hd)
    v _ (neg_ne_zero.mpr hl) hv
  have hx := hc 0
  have hy := hc 1
  change x - φ h = φ (ct (x - φ h)) at hx
  change y - φ k = φ (ct (y - φ k)) at hy
  simp only [φ, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply] at hx hy
  constructor
  · linear_combination hx
  · linear_combination hy

end
end Surreal.CentralConic
