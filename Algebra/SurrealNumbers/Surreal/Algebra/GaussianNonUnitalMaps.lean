import Surreal.Algebra.OrdinaryRingMaps

/-!
# Nonunital maps from the ordinary Gaussian integers

The algebra behind the nonunital consequence following `osq:cor:gaussian`.
The target need not have an identity or commutative multiplication. The
images e of one and j of i satisfy exactly ee=e, ej=je=j and jj=-e.
-/

universe u
namespace Surreal.OrdinaryRingMaps
noncomputable section

/-- The complete pair of parameters for a nonunital Gaussian map. -/
def GaussianPair (S : Type u) [NonUnitalRing S] :=
  {p : S × S // p.1 * p.1 = p.1 ∧ p.1 * p.2 = p.2 ∧
    p.2 * p.1 = p.2 ∧ p.2 * p.2 = -p.1}

/-- Evaluation at a compatible idempotent and imaginary element. -/
def gaussianNonUnitalMap {S : Type u} [NonUnitalRing S] (p : GaussianPair S) :
    GaussianInt →ₙ+* S where
  toFun z := z.re • p.val.1 + z.im • p.val.2
  map_zero' := by simp
  map_add' z w := by
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, add_zsmul]
    abel
  map_mul' z w := by
    have hm (a b : ℤ) (x y : S) : (a • x) * (b • y) = (a * b) • (x * y) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, add_mul, mul_add, hm,
      p.property.1, p.property.2.1, p.property.2.2.1, p.property.2.2.2,
      add_zsmul, neg_mul, one_mul, neg_zsmul, smul_neg]
    abel

/-- The first parameter is the image of one. -/
@[simp] theorem gaussianNonUnitalMap_one {S : Type u} [NonUnitalRing S] (p : GaussianPair S) :
    gaussianNonUnitalMap p 1 = p.val.1 := by
  change (1 : ℤ) • p.val.1 + (0 : ℤ) • p.val.2 = p.val.1
  simp

/-- The second parameter is the image of the ordinary imaginary unit. -/
@[simp] theorem gaussianNonUnitalMap_sqrtd {S : Type u} [NonUnitalRing S] (p : GaussianPair S) :
    gaussianNonUnitalMap p Zsqrtd.sqrtd = p.val.2 := by
  change (0 : ℤ) • p.val.1 + (1 : ℤ) • p.val.2 = p.val.2
  simp

/-- A nonunital Gaussian map has the coordinate formula from its two additive basis images. -/
theorem gaussian_nonunital_coordinates {S : Type u} [NonUnitalRing S]
    (φ : GaussianInt →ₙ+* S) (z : GaussianInt) :
    φ z = z.re • φ 1 + z.im • φ Zsqrtd.sqrtd := by
  have he : z = z.re • (1 : GaussianInt) + z.im • Zsqrtd.sqrtd := by
    apply Zsqrtd.ext <;> simp
  conv_lhs => rw [he, map_add, map_zsmul, map_zsmul]

/-- Nonunital Gaussian maps correspond bijectively to precisely the displayed compatible pairs. -/
def gaussianNonUnitalHomEquiv (S : Type u) [NonUnitalRing S] :
    (GaussianInt →ₙ+* S) ≃ GaussianPair S where
  toFun φ := ⟨(φ 1, φ Zsqrtd.sqrtd), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← map_mul, one_mul]
    · rw [← map_mul, one_mul]
    · rw [← map_mul, mul_one]
    · rw [← map_mul, Zsqrtd.dmuld]
      change φ (-1) = -φ 1
      exact map_neg φ 1⟩
  invFun := gaussianNonUnitalMap
  left_inv φ := by
    ext z
    exact (gaussian_nonunital_coordinates φ z).symm
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (gaussianNonUnitalMap_one p) (gaussianNonUnitalMap_sqrtd p)

/-- For a unital target, the nonunital map preserves one exactly when e is its identity. -/
theorem gaussianNonUnitalMap_preserves_one_iff {S : Type u} [Ring S] (p : GaussianPair S) :
    gaussianNonUnitalMap p 1 = 1 ↔ p.val.1 = 1 := by
  rw [gaussianNonUnitalMap_one]

end
end Surreal.OrdinaryRingMaps
