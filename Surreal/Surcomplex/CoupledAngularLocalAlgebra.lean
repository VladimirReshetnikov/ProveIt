import Surreal.Algebra.CoupledQuadraticSplit
import Surreal.Algebra.CoupledQuadraticLocal
import Surreal.Surcomplex.CoupledAngularRoots

/-!
# Actual local algebra factors for the coupled angular collision

The finite intersection algebra from `trigonometry:sec:coupled` decomposes
into local factors of dimension one, two or four, with the stated supports.
The sum of these dimensions is four on every stratum. Transport of these
algebraic dimensions through the analytic angular coordinate germs remains
a separate obligation; no definition here silently identifies the two.
-/

universe u

namespace Surreal.Surcomplex.CoupledAngular

open FinitePolynomial

noncomputable section

/-- The actual finite algebra of the diagonal equations. -/
abbrev IntersectionAlgebra (s t : Surcomplex.{u}) :=
  coupledQuotient (s + 2 * t) (s - 2 * t)

/-- Away from both diagonal collisions there are four local field factors. -/
theorem separated_local_factors (s t : Surcomplex.{u})
    (hp : s + 2 * t ≠ 0) (hq : s - 2 * t ≠ 0) :
    Nonempty (IntersectionAlgebra s t ≃ₐ[Surcomplex.{u}]
      (Surcomplex.{u} × Surcomplex.{u}) × (Surcomplex.{u} × Surcomplex.{u})) ∧
    IsLocalRing Surcomplex.{u} ∧ Module.finrank Surcomplex.{u} Surcomplex.{u} = 1 := by
  obtain ⟨p, hps⟩ := QuadraticCollision.exists_point (s + 2 * t)
  obtain ⟨q, hqs⟩ := QuadraticCollision.exists_point (s - 2 * t)
  have hp0 : p ≠ 0 := fun h => hp (by simpa [h] using hps.symm)
  have hq0 : q ≠ 0 := fun h => hq (by simpa [h] using hqs.symm)
  exact ⟨⟨coupledSeparated _ _ p q hps hqs hp0 hq0⟩, inferInstance, Module.finrank_self _⟩

/-- A single collision gives two local dual-number factors, each of dimension two. -/
theorem single_collision_local_factors (s t : Surcomplex.{u})
    (h : (s + 2 * t = 0 ∧ s - 2 * t ≠ 0) ∨
      (s + 2 * t ≠ 0 ∧ s - 2 * t = 0)) :
    Nonempty (IntersectionAlgebra s t ≃ₐ[Surcomplex.{u}]
      DualNumber Surcomplex.{u} × DualNumber Surcomplex.{u}) ∧
    IsLocalRing (DualNumber Surcomplex.{u}) ∧
      Module.finrank Surcomplex.{u} (DualNumber Surcomplex.{u}) = 2 := by
  refine ⟨?_, dualNumber_isLocalRing, dualNumber_finrank⟩
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · obtain ⟨q, hqs⟩ := QuadraticCollision.exists_point (s - 2 * t)
    have hq0 : q ≠ 0 := fun h => hq (by simpa [h] using hqs.symm)
    change Nonempty (coupledQuotient _ _ ≃ₐ[Surcomplex.{u}] _)
    rw [hp]
    exact ⟨coupledSingleCollisionRight _ q hqs hq0⟩
  · obtain ⟨p, hps⟩ := QuadraticCollision.exists_point (s + 2 * t)
    have hp0 : p ≠ 0 := fun h => hp (by simpa [h] using hps.symm)
    change Nonempty (coupledQuotient _ _ ≃ₐ[Surcomplex.{u}] _)
    rw [hq]
    exact ⟨coupledSingleCollisionLeft _ p hps hp0⟩

/-- At the common collision the rank-four algebra is already a single local factor. -/
theorem common_collision_local_factor :
    IsLocalRing (IntersectionAlgebra (0 : Surcomplex.{u}) 0) ∧
      Module.finrank Surcomplex.{u} (IntersectionAlgebra (0 : Surcomplex.{u}) 0) = 4 := by
  exact ⟨coupled_isLocalRing_of_eq_zero _ _ (by ring) (by ring), intersection_finrank 0 0⟩

/-- The common dimension of the local factors on each diagonal stratum.
The preceding decomposition theorems certify its meaning as a native algebra dimension. -/
def localFactorDimension (s t : Surcomplex.{u}) : ℕ :=
  (if s + 2 * t = 0 then 2 else 1) * (if s - 2 * t = 0 then 2 else 1)

/-- Off the discriminant every local factor is a one-dimensional field. -/
theorem localFactorDimension_separated (s t : Surcomplex.{u})
    (hp : s + 2 * t ≠ 0) (hq : s - 2 * t ≠ 0) :
    localFactorDimension s t = Module.finrank Surcomplex.{u} Surcomplex.{u} := by
  simp [localFactorDimension, hp, hq]

/-- On a single-collision stratum this is the dimension of either dual-number factor. -/
theorem localFactorDimension_single (s t : Surcomplex.{u})
    (h : (s + 2 * t = 0 ∧ s - 2 * t ≠ 0) ∨
      (s + 2 * t ≠ 0 ∧ s - 2 * t = 0)) :
    localFactorDimension s t = Module.finrank Surcomplex.{u} (DualNumber Surcomplex.{u}) := by
  rw [dualNumber_finrank]
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> simp [localFactorDimension, hp, hq]

/-- At the origin there is just one factor and it retains all four dimensions. -/
theorem localFactorDimension_zero :
    localFactorDimension (0 : Surcomplex.{u}) 0 =
      Module.finrank Surcomplex.{u} (IntersectionAlgebra (0 : Surcomplex.{u}) 0) := by
  rw [intersection_finrank]
  norm_num [localFactorDimension]

/-- Counting each actual infinitesimal support point with the dimension of
its algebraic local factor always yields four. Analytic transport is not assumed. -/
theorem total_local_dimensions (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) :
    Nat.card (Solutions s t) * localFactorDimension s t = 4 := by
  rw [card_solutions s t hs ht]
  by_cases hp : s + 2 * t = 0 <;> by_cases hq : s - 2 * t = 0 <;>
    simp [localFactorDimension, hp, hq]

/-- The counted local dimensions agree with the dimension of the full intersection algebra. -/
theorem total_local_dimensions_eq_finrank (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) :
    Nat.card (Solutions s t) * localFactorDimension s t =
      Module.finrank Surcomplex.{u} (IntersectionAlgebra s t) := by
  rw [total_local_dimensions s t hs ht, intersection_finrank]

end
end Surreal.Surcomplex.CoupledAngular
