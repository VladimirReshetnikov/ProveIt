import Surreal.Algebra.BinaryFormRigidity

/-!
# Quadratic norm rigidity in constant-unit algebras

The factorization step of `odg:def:cor:pell`. A chosen nonzero square root
and invertibility of 2 suffice; the ambient algebra need not be a domain.
-/

namespace Surreal.QuadraticNormRigidity

noncomputable section

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [Algebra K B]

/-- A nonzero split quadratic norm level has constant coordinates whenever all units
of the algebra are constants. -/
theorem coordinates_constant (ct : B →ₐ[K] K)
    (hunit : ∀ z : B, IsUnit z → z = algebraMap K B (ct z))
    (r c : K) (hr : r ≠ 0) (hc : c ≠ 0) (x y : B)
    (h : x ^ 2 - algebraMap K B (r ^ 2) * y ^ 2 = algebraMap K B c) :
    x = algebraMap K B (ct x) ∧ y = algebraMap K B (ct y) := by
  let C := algebraMap K B
  have hf : (x + C r * y) * (x - C r * y) = C c := by
    dsimp [C]
    rw [map_pow] at h
    linear_combination h
  have hu : IsUnit ((x + C r * y) * (x - C r * y)) :=
    hf ▸ (isUnit_iff_ne_zero.mpr hc).map C
  have hp := hunit _ (isUnit_of_mul_isUnit_left hu)
  have hm := hunit _ (isUnit_of_mul_isUnit_right hu)
  simp only [C, map_add, map_sub, map_mul, AlgHom.commutes,
    Algebra.algebraMap_self_apply] at hp hm
  have htwo : IsUnit (C 2) := (isUnit_iff_ne_zero.mpr two_ne_zero).map C
  have htwor : IsUnit (C (2 * r)) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero two_ne_zero hr)).map C
  constructor
  · apply sub_eq_zero.mp
    apply htwo.mul_left_cancel
    rw [mul_zero]
    change algebraMap K B 2 * (x - algebraMap K B (ct x)) = 0
    rw [map_ofNat]
    linear_combination hp + hm
  · apply sub_eq_zero.mp
    apply htwor.mul_left_cancel
    rw [mul_zero]
    change algebraMap K B (2 * r) * (y - algebraMap K B (ct y)) = 0
    rw [map_mul, map_ofNat]
    linear_combination hp - hm

end
end Surreal.QuadraticNormRigidity
