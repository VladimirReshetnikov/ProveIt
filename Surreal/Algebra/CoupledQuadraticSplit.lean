import Surreal.Algebra.CoupledQuadraticAlgebra
import Surreal.Algebra.QuadraticSplit
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Product decompositions of the coupled quadratic algebra

These are the separated and single-collision local factors in
`trigonometry:sec:coupled`. Evaluation at either pair of roots splits off
quadratic factors without discarding their nilpotents. At a single collision
there are two dual-number factors; off the collision locus there are four
field factors, each of dimension one.
-/

namespace Surreal.FinitePolynomial

open scoped TensorProduct

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Splitting the second quadratic gives two copies of the first quotient. -/
def coupledSplitRight (a b q : K) (hq : q ^ 2 = b) (hq0 : q ≠ 0) :
    coupledQuotient a b ≃ₐ[K] quadraticQuotient a × quadraticQuotient a :=
  (Algebra.TensorProduct.congr ((AlgEquiv.refl : quadraticQuotient a ≃ₐ[K] quadraticQuotient a))
    (quadraticSplitEquiv b q hq hq0)).trans
      ((Algebra.TensorProduct.prodRight K K (quadraticQuotient a) K K).trans
        (AlgEquiv.prodCongr (Algebra.TensorProduct.rid K K (quadraticQuotient a))
          (Algebra.TensorProduct.rid K K (quadraticQuotient a))))

/-- Evaluation in the second coordinate leaves the first generator unchanged. -/
@[simp] theorem coupledSplitRight_X (a b q : K) (hq : q ^ 2 = b) (hq0 : q ≠ 0) :
    coupledSplitRight a b q hq hq0 (coupledX a b) = (quadraticRoot a, quadraticRoot a) := by
  simp [coupledSplitRight, coupledX, Algebra.TensorProduct.prodRight_tmul]

/-- The two factors lie at the two indicated values of the second coordinate. -/
@[simp] theorem coupledSplitRight_Y (a b q : K) (hq : q ^ 2 = b) (hq0 : q ≠ 0) :
    coupledSplitRight a b q hq hq0 (coupledY a b) =
      (algebraMap K _ q, algebraMap K _ (-q)) := by
  simp [coupledSplitRight, coupledY, Algebra.TensorProduct.prodRight_tmul, Algebra.smul_def]

/-- Interchange the two coordinates, retaining their algebra relations. -/
def coupledSwap (a b : K) : coupledQuotient a b ≃ₐ[K] coupledQuotient b a :=
  Algebra.TensorProduct.comm K (quadraticQuotient a) (quadraticQuotient b)

omit [CharZero K] in
@[simp] theorem coupledSwap_X (a b : K) :
    coupledSwap a b (coupledX a b) = coupledY b a := by
  simp [coupledSwap, coupledX, coupledY]

omit [CharZero K] in
@[simp] theorem coupledSwap_Y (a b : K) :
    coupledSwap a b (coupledY a b) = coupledX b a := by
  simp [coupledSwap, coupledX, coupledY]

/-- Splitting the first quadratic gives two copies of the second quotient. -/
def coupledSplitLeft (a b p : K) (hp : p ^ 2 = a) (hp0 : p ≠ 0) :
    coupledQuotient a b ≃ₐ[K] quadraticQuotient b × quadraticQuotient b :=
  (coupledSwap a b).trans (coupledSplitRight b a p hp hp0)

/-- At a single collision the two local factors are exactly dual numbers. -/
def coupledSingleCollisionRight (b q : K) (hq : q ^ 2 = b) (hq0 : q ≠ 0) :
    coupledQuotient 0 b ≃ₐ[K] DualNumber K × DualNumber K :=
  (coupledSplitRight 0 b q hq hq0).trans (AlgEquiv.prodCongr quadraticDualEquiv quadraticDualEquiv)

/-- The same local decomposition with the first coordinate separated. -/
def coupledSingleCollisionLeft (a p : K) (hp : p ^ 2 = a) (hp0 : p ≠ 0) :
    coupledQuotient a 0 ≃ₐ[K] DualNumber K × DualNumber K :=
  (coupledSwap a 0).trans (coupledSingleCollisionRight a p hp hp0)

/-- Off both collisions the algebra is the product of four residue fields. -/
def coupledSeparated (a b p q : K) (hp : p ^ 2 = a) (hq : q ^ 2 = b)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    coupledQuotient a b ≃ₐ[K] (K × K) × (K × K) :=
  (coupledSplitRight a b q hq hq0).trans
    (AlgEquiv.prodCongr (quadraticSplitEquiv a p hp hp0) (quadraticSplitEquiv a p hp hp0))

/-- The four field factors have their literal first root coordinates. -/
@[simp] theorem coupledSeparated_X (a b p q : K) (hp : p ^ 2 = a) (hq : q ^ 2 = b)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    coupledSeparated a b p q hp hq hp0 hq0 (coupledX a b) = ((p, -p), (p, -p)) := by
  simp [coupledSeparated]

/-- The four field factors have their literal second root coordinates. -/
@[simp] theorem coupledSeparated_Y (a b p q : K) (hp : p ^ 2 = a) (hq : q ^ 2 = b)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    coupledSeparated a b p q hp hq hp0 hq0 (coupledY a b) = ((q, q), (-q, -q)) := by
  simp only [coupledSeparated, AlgEquiv.trans_apply, coupledSplitRight_Y,
    AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply, Prod.map_apply]
  change (quadraticSplitEquiv a p hp hp0 (algebraMap K _ q),
    quadraticSplitEquiv a p hp hp0 (algebraMap K _ (-q))) = _
  rw [AlgEquiv.commutes, AlgEquiv.commutes]
  rfl

/-- The surviving infinitesimal direction at a single collision is the
nonzero dual-number generator in each factor. -/
@[simp] theorem coupledSingleCollisionRight_X (b q : K) (hq : q ^ 2 = b) (hq0 : q ≠ 0) :
    coupledSingleCollisionRight b q hq hq0 (coupledX 0 b) = (DualNumber.eps, DualNumber.eps) := by
  simp only [coupledSingleCollisionRight, AlgEquiv.trans_apply, coupledSplitRight_X,
    AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply, Prod.map_apply]
  exact Prod.ext quadraticToDual_root quadraticToDual_root

/-- Each single-collision factor is supported at its specified separated coordinate. -/
@[simp] theorem coupledSingleCollisionRight_Y (b q : K) (hq : q ^ 2 = b) (hq0 : q ≠ 0) :
    coupledSingleCollisionRight b q hq hq0 (coupledY 0 b) =
      (algebraMap K _ q, algebraMap K _ (-q)) := by
  simp only [coupledSingleCollisionRight, AlgEquiv.trans_apply, coupledSplitRight_Y,
    AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply, Prod.map_apply]
  change (quadraticDualEquiv (algebraMap K _ q), quadraticDualEquiv (algebraMap K _ (-q))) = _
  rw [AlgEquiv.commutes, AlgEquiv.commutes]

/-- The left-separated single-collision factors have the corresponding root supports. -/
@[simp] theorem coupledSingleCollisionLeft_X (a p : K) (hp : p ^ 2 = a) (hp0 : p ≠ 0) :
    coupledSingleCollisionLeft a p hp hp0 (coupledX a 0) =
      (algebraMap K _ p, algebraMap K _ (-p)) := by
  rw [coupledSingleCollisionLeft, AlgEquiv.trans_apply,
    coupledSwap_X, coupledSingleCollisionRight_Y]

/-- The other coordinate remains the nonzero nilpotent in both local factors. -/
@[simp] theorem coupledSingleCollisionLeft_Y (a p : K) (hp : p ^ 2 = a) (hp0 : p ≠ 0) :
    coupledSingleCollisionLeft a p hp hp0 (coupledY a 0) = (DualNumber.eps, DualNumber.eps) := by
  rw [coupledSingleCollisionLeft, AlgEquiv.trans_apply,
    coupledSwap_Y, coupledSingleCollisionRight_X]

end
end Surreal.FinitePolynomial
