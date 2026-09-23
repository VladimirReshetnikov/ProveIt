import Surreal.Algebra.QuadraticLineCircle
import Surreal.Algebra.QuadraticDualNumber
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Local factors of a quadratic collision

For the local decomposition in `trigonometry:sec:coupled`, a quadratic
with two distinct roots is the product of its two residue fields. At the
collision it is the dual numbers, a local algebra of dimension two.
The separated equivalence is evaluation at the two actual roots.
-/

namespace Surreal.FinitePolynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Evaluation at a chosen root as a native algebra homomorphism. -/
def quadraticEvaluation (d s : K) (hs : s ^ 2 = d) : quadraticQuotient d →ₐ[K] K :=
  (quadraticHomEquivRoots d K).symm ⟨s, hs⟩

@[simp] theorem quadraticEvaluation_root (d s : K) (hs : s ^ 2 = d) :
    quadraticEvaluation d s hs (quadraticRoot d) = s :=
  quadraticHomEquivRoots_symm_root d K _

/-- Evaluation retains exactly the two remainder coordinates. -/
theorem quadraticEvaluation_apply (d s : K) (hs : s ^ 2 = d) (z : quadraticQuotient d) :
    quadraticEvaluation d s hs z = quadraticConstant d z + quadraticResidue d z * s := by
  conv_lhs => rw [quadratic_eq_scalar_add_mul_root d z]
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, quadraticEvaluation_root]
  rfl

/-- Evaluate independently at the two separated roots. -/
def quadraticEvaluationPair (d s : K) (hs : s ^ 2 = d) : quadraticQuotient d →ₐ[K] K × K :=
  (quadraticEvaluation d s hs).prod (quadraticEvaluation d (-s) (by simpa using hs))

section Split

variable [CharZero K]

/-- The separated quadratic is exactly the product of its two field factors. -/
def quadraticSplitEquiv (d s : K) (hs : s ^ 2 = d) (hs0 : s ≠ 0) :
    quadraticQuotient d ≃ₐ[K] K × K :=
  AlgEquiv.ofBijective (quadraticEvaluationPair d s hs) ⟨by
    intro z w h
    have hp := congrArg Prod.fst h
    have hm := congrArg Prod.snd h
    change quadraticEvaluation d s hs z = quadraticEvaluation d s hs w at hp
    change quadraticEvaluation d (-s) _ z = quadraticEvaluation d (-s) _ w at hm
    simp only [quadraticEvaluation_apply] at hp hm
    apply quadratic_ext
    · linear_combination (hp + hm) / 2
    · apply (mul_right_cancel₀ hs0)
      linear_combination (hp - hm) / 2, by
    intro ab
    refine ⟨algebraMap K _ ((ab.1 + ab.2) / 2) +
      algebraMap K _ ((ab.1 - ab.2) / (2 * s)) * quadraticRoot d, ?_⟩
    apply Prod.ext
    · change quadraticEvaluation d s hs _ = ab.1
      rw [quadraticEvaluation_apply, quadraticConstant_scalar_add_mul_root,
        quadraticResidue_scalar_add_mul_root]
      field_simp; ring
    · change quadraticEvaluation d (-s) _ _ = ab.2
      rw [quadraticEvaluation_apply, quadraticConstant_scalar_add_mul_root,
        quadraticResidue_scalar_add_mul_root]
      field_simp; ring⟩

@[simp] theorem quadraticSplitEquiv_root (d s : K) (hs : s ^ 2 = d) (hs0 : s ≠ 0) :
    quadraticSplitEquiv d s hs hs0 (quadraticRoot d) = (s, -s) := by
  apply Prod.ext <;> exact quadraticEvaluation_root _ _ _

end Split

/-- The residue at the unique collision point is the constant coordinate. -/
theorem quadraticEvaluation_zero (z : quadraticQuotient (0 : K)) :
    quadraticEvaluation 0 0 (by simp) z = quadraticConstant 0 z := by
  rw [quadraticEvaluation_apply, mul_zero, add_zero]

/-- A dual number over a field is invertible exactly when its constant term is nonzero. -/
theorem dualNumber_isUnit_iff (z : DualNumber K) : IsUnit z ↔ z.fst ≠ 0 := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]

/-- The dual-number algebra is local, so its dimension two is a local dimension. -/
theorem dualNumber_isLocalRing : IsLocalRing (DualNumber K) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro z
  by_cases h : z.fst = 0
  · right
    rw [dualNumber_isUnit_iff]
    simp [h]
  · exact Or.inl ((dualNumber_isUnit_iff z).mpr h)

/-- The dual-number factor has dimension two over its residue field. -/
theorem dualNumber_finrank : Module.finrank K (DualNumber K) = 2 := by
  rw [← quadraticDualEquiv.toLinearEquiv.finrank_eq]
  exact quadraticQuotient_finrank 0

end
end Surreal.FinitePolynomial
