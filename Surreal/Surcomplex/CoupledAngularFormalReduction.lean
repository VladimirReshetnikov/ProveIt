import Surreal.Algebra.FormalCoupledDiagonal
import Surreal.Surcomplex.CoupledAngularFormalCoordinates

/-!
# The coupled angular germ as a truncated formal algebra

At every actual infinitesimal solution of `trigonometry:eq:coupled`, the
angular formal quotient is isomorphic to the quotient by two pure variable
powers. Each power is two precisely on its diagonal collision, otherwise
one. This transports the entire ideal, including nilpotents. The native
dimension is computed in `CoupledAngularMultiplicity.lean`.
-/

universe u

namespace Surreal.Surcomplex.CoupledAngular

open MvPowerSeries FormalCoupled

noncomputable section

/-- The root equation removes exactly the constant terms of the polynomial ideal. -/
theorem polynomialIdeal_at_root (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    polynomialIdeal s t θ hθ =
      Ideal.span {first (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1)),
        second (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))} := by
  rw [polynomialIdeal, polynomialFirst_at_root s t θ hθ he,
    polynomialSecond_at_root s t θ hθ he]
  rfl

/-- At a root, a zero diagonal coordinate is equivalent to a zero diagonal parameter. -/
theorem diagonal_coordinate_zero_iff (s t x y : Surcomplex.{u}) (he : Equations s t x y) :
    (x + y = 0 ↔ s + 2 * t = 0) ∧ (x - y = 0 ↔ s - 2 * t = 0) := by
  obtain ⟨hp, hq⟩ := (equations_iff s t x y).mp he
  constructor
  · rw [← hp, sq_eq_zero_iff]
  · rw [← hq, sq_eq_zero_iff]

/-- The truncation orders depend only on the parameter stratum, not the chosen root. -/
theorem local_exponents_at_root (s t x y : Surcomplex.{u}) (he : Equations s t x y) :
    localExponent (x + y) = localExponent (s + 2 * t) ∧
      localExponent (x - y) = localExponent (s - 2 * t) := by
  obtain ⟨hp, hq⟩ := diagonal_coordinate_zero_iff s t x y he
  by_cases hs : s + 2 * t = 0 <;> by_cases ht : s - 2 * t = 0 <;>
    simp [localExponent, hp, hq, hs, ht]

/-- The explicit monomial ideal retaining the two collision directions. -/
def truncatedIdeal (s t : Surcomplex.{u}) : Ideal FormalRing.{u} :=
  Ideal.span {X 0 ^ localExponent (s + 2 * t), X 1 ^ localExponent (s - 2 * t)}

/-- Every centered angular quotient is algebraically equivalent to its monomial truncation.
The equivalence composes unit-factor removal, linear diagonalization and the verified sine germ. -/
def truncatedAngularEquiv (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    (FormalRing.{u} ⧸ truncatedIdeal s t) ≃ₐ[Surcomplex.{u}]
      FormalRing.{u} ⧸ angularIdeal s t θ hθ := by
  have hh := local_exponents_at_root s t _ _ he
  have hi : truncatedIdeal s t =
      Ideal.span {(X 0 : FormalRing.{u}) ^
        localExponent (infSin (θ 0) (hθ 0) + infSin (θ 1) (hθ 1)),
        X 1 ^ localExponent (infSin (θ 0) (hθ 0) - infSin (θ 1) (hθ 1))} := by
    rw [hh.1, hh.2]
    rfl
  exact (Ideal.quotientEquivAlgOfEq Surcomplex.{u} hi).trans
    ((truncatedQuotientEquiv _ _).trans
      ((Ideal.quotientEquivAlgOfEq Surcomplex.{u} (polynomialIdeal_at_root s t θ hθ he).symm).trans
        (formalQuotientEquiv s t θ hθ)))

/-- The angular formal algebra has exactly the native dimension of its monomial truncation. -/
theorem angular_finrank_eq_truncated (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    Module.finrank Surcomplex.{u} (FormalRing.{u} ⧸ angularIdeal s t θ hθ) =
      Module.finrank Surcomplex.{u} (FormalRing.{u} ⧸ truncatedIdeal s t) :=
  (truncatedAngularEquiv s t θ hθ he).toLinearEquiv.finrank_eq.symm

end
end Surreal.Surcomplex.CoupledAngular
