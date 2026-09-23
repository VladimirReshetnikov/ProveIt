import Surreal.Algebra.CoupledQuadraticAlgebra
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The local algebra at the common coupled collision

At the origin of `trigonometry:sec:coupled`, the entire rank-four algebra
is local. Its residue map evaluates both generators at zero, and its kernel
consists of nilpotents. This proves that the rank four belongs to one local
factor, rather than merely to a four-dimensional algebra with unknown support.
-/

namespace Surreal.FinitePolynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Evaluation at the unique point of the common collision. -/
def coupledCollisionResidue : coupledQuotient (0 : K) 0 →ₐ[K] K :=
  (coupledHomEquivRoots 0 0 K).symm (⟨0, by simp⟩, ⟨0, by simp⟩)

@[simp] theorem coupledCollisionResidue_X :
    coupledCollisionResidue (coupledX (0 : K) 0) = 0 := by
  change ((coupledHomEquivRoots 0 0 K)
    ((coupledHomEquivRoots 0 0 K).symm (⟨0, by simp⟩, ⟨0, by simp⟩))).1.1 = 0
  rw [Equiv.apply_symm_apply]

@[simp] theorem coupledCollisionResidue_Y :
    coupledCollisionResidue (coupledY (0 : K) 0) = 0 := by
  change ((coupledHomEquivRoots 0 0 K)
    ((coupledHomEquivRoots 0 0 K).symm (⟨0, by simp⟩, ⟨0, by simp⟩))).2.1 = 0
  rw [Equiv.apply_symm_apply]

/-- A convenient literal version of the four-coordinate remainder. -/
theorem coupled_representation (a b : K) (z : coupledQuotient a b) :
    ∃ c₀ c₁ c₂ c₃ : K, z = algebraMap K _ c₀ + algebraMap K _ c₁ * coupledX a b +
      algebraMap K _ c₂ * coupledY a b + algebraMap K _ c₃ * coupledX a b * coupledY a b := by
  obtain ⟨c, hc, _⟩ := existsUnique_coupled_representation a b z
  refine ⟨c (0, 0), c (1, 0), c (0, 1), c (1, 1), ?_⟩
  rw [hc]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_mul, mul_one, Algebra.smul_def]
  ring

/-- Both coordinate directions are nilpotent at the common collision. -/
theorem coupledCollision_X_nilpotent : IsNilpotent (coupledX (0 : K) 0) :=
  ⟨2, by rw [coupledX_sq, map_zero]⟩

theorem coupledCollision_Y_nilpotent : IsNilpotent (coupledY (0 : K) 0) :=
  ⟨2, by rw [coupledY_sq, map_zero]⟩

/-- Every element differs from its residue by a nilpotent. -/
theorem coupledCollision_remainder_nilpotent (z : coupledQuotient (0 : K) 0) :
    IsNilpotent (z - algebraMap K _ (coupledCollisionResidue z)) := by
  obtain ⟨a, b, c, d, rfl⟩ := coupled_representation 0 0 z
  simp only [map_add, map_mul, AlgHom.commutes, coupledCollisionResidue_X,
    coupledCollisionResidue_Y, mul_zero, add_zero, Algebra.algebraMap_self, RingHom.id_apply]
  rw [show algebraMap K (coupledQuotient (0 : K) 0) a +
      algebraMap K _ b * coupledX 0 0 + algebraMap K _ c * coupledY 0 0 +
      algebraMap K _ d * coupledX 0 0 * coupledY 0 0 - algebraMap K _ a =
      algebraMap K _ b * coupledX 0 0 + algebraMap K _ c * coupledY 0 0 +
      algebraMap K _ d * coupledX 0 0 * coupledY 0 0 by ring]
  apply (Commute.all _ _).isNilpotent_add
  · exact (Commute.all _ _).isNilpotent_add
      ((Commute.all _ _).isNilpotent_mul_left coupledCollision_X_nilpotent)
      ((Commute.all _ _).isNilpotent_mul_left coupledCollision_Y_nilpotent)
  · exact (Commute.all _ _).isNilpotent_mul_left coupledCollision_Y_nilpotent

/-- Units are exactly the elements with nonzero residue. -/
theorem coupledCollision_isUnit_iff (z : coupledQuotient (0 : K) 0) :
    IsUnit z ↔ coupledCollisionResidue z ≠ 0 := by
  constructor
  · intro hz
    exact (hz.map coupledCollisionResidue).ne_zero
  · intro hz
    have hu : IsUnit (algebraMap K (coupledQuotient (0 : K) 0) (coupledCollisionResidue z)) :=
      (isUnit_iff_ne_zero.mpr hz).map (algebraMap K _)
    simpa only [add_sub_cancel] using
      (coupledCollision_remainder_nilpotent z).isUnit_add_left_of_commute hu (Commute.all _ _)

/-- The rank-four common-collision algebra is a single local ring. -/
theorem coupledCollision_isLocalRing : IsLocalRing (coupledQuotient (0 : K) 0) := by
  letI : Nontrivial (coupledQuotient (0 : K) 0) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [coupledQuotient_finrank]; norm_num)
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro z
  by_cases h : coupledCollisionResidue z = 0
  · right
    rw [coupledCollision_isUnit_iff]
    simp [h]
  · exact Or.inl ((coupledCollision_isUnit_iff z).mpr h)

/-- Locality transports along equalities of the two collision parameters. -/
theorem coupled_isLocalRing_of_eq_zero (a b : K) (ha : a = 0) (hb : b = 0) :
    IsLocalRing (coupledQuotient a b) := by
  subst a
  subst b
  exact coupledCollision_isLocalRing

/-- The unique local factor has dimension four. -/
theorem coupledCollision_local_dimension :
    IsLocalRing (coupledQuotient (0 : K) 0) ∧
      Module.finrank K (coupledQuotient (0 : K) 0) = 4 :=
  ⟨coupledCollision_isLocalRing, coupledQuotient_finrank 0 0⟩

/-- The residue field is the coefficient field itself, with every scalar attained. -/
theorem coupledCollisionResidue_surjective :
    Function.Surjective (coupledCollisionResidue (K := K)) := by
  intro k
  exact ⟨algebraMap K _ k, coupledCollisionResidue.commutes k⟩

/-- The kernel of evaluation is the unique maximal ideal at the common collision. -/
theorem coupledCollision_unique_maximal_ideal :
    (RingHom.ker (coupledCollisionResidue (K := K)).toRingHom).IsMaximal ∧
      ∀ I : Ideal (coupledQuotient (0 : K) 0), I.IsMaximal →
        I = RingHom.ker coupledCollisionResidue.toRingHom := by
  letI := coupledCollision_isLocalRing (K := K)
  have h := RingHom.ker_isMaximal_of_surjective
    (coupledCollisionResidue (K := K)).toRingHom coupledCollisionResidue_surjective
  exact ⟨h, fun _ hI => (IsLocalRing.eq_maximalIdeal hI).trans
    (IsLocalRing.eq_maximalIdeal h).symm⟩

end
end Surreal.FinitePolynomial
