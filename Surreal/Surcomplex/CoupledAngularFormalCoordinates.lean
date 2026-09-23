import Surreal.Algebra.FormalCoordinateChange
import Surreal.Surcomplex.LocalSineSeries
import Surreal.Surcomplex.CoupledAngularRoots

/-!
# Formal local angular coordinates at every coupled root

For `trigonometry:sec:coupled`, each actual centered sine germ has a unit
linear coefficient. Mathlib's compositional inverse induces an automorphism
of the two-variable formal series ring. The two translated polynomial
relations map to the corresponding angular series relations, so their
quotient algebras are isomorphic and have equal native dimensions.
`CoupledAngularFormalReduction.lean` reduces these quotients to monomial
ideals; `CoupledAngularMultiplicity.lean` computes their native dimensions.
-/

universe u

namespace Surreal.Surcomplex.CoupledAngular

open MvPowerSeries

noncomputable section

/-- The formal increment ring over the actual surcomplex coefficient field. -/
abbrev FormalRing := MvPowerSeries (Fin 2) Surcomplex.{u}

/-- Each component is a verified strong expansion at its actual angle center. -/
def sineGerms (θ : Fin 2 → Surcomplex.{u}) (hθ : ∀ i, IsInfinitesimal (θ i)) :
    Fin 2 → PowerSeries Surcomplex.{u} := fun i => localSinSeries (θ i) (hθ i)

/-- The formal angular change of variables is invertible at every infinitesimal center. -/
def sineCoordinateChange (θ : Fin 2 → Surcomplex.{u}) (hθ : ∀ i, IsInfinitesimal (θ i)) :
    FormalRing.{u} ≃ₐ[Surcomplex.{u}] FormalRing.{u} :=
  FormalCoordinate.ofUnitLinear (sineGerms θ hθ)
    (fun i => constantCoeff_localSinSeries (θ i) (hθ i))
    (fun i => isUnit_linear_localSinSeries (θ i) (hθ i))

/-- The sine increment in a specified formal variable. -/
def sineIncrement (θ : Fin 2 → Surcomplex.{u}) (hθ : ∀ i, IsInfinitesimal (θ i))
    (i : Fin 2) : FormalRing.{u} := FormalCoordinate.coordinates (sineGerms θ hθ) i

@[simp] theorem sineCoordinateChange_X (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) (i : Fin 2) :
    sineCoordinateChange θ hθ (X i) = sineIncrement θ hθ i :=
  FormalCoordinate.ofUnitLinear_X _ _ _ i

@[simp] theorem sineCoordinateChange_C (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) (c : Surcomplex.{u}) :
    sineCoordinateChange θ hθ (C c) = C c := (sineCoordinateChange θ hθ).commutes c

@[simp] theorem constantCoeff_sineIncrement (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) (i : Fin 2) :
    constantCoeff (sineIncrement θ hθ i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (constantCoeff_localSinSeries _ _)

/-- The first polynomial relation translated to the sine-coordinate point. -/
def polynomialFirst (s : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) : FormalRing.{u} :=
  (C (infSin (θ 0) (hθ 0)) + X 0) ^ 2 +
    (C (infSin (θ 1) (hθ 1)) + X 1) ^ 2 - C s

/-- The second polynomial relation translated to the sine-coordinate point. -/
def polynomialSecond (t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) : FormalRing.{u} :=
  (C (infSin (θ 0) (hθ 0)) + X 0) * (C (infSin (θ 1) (hθ 1)) + X 1) - C t

/-- The first relation in the verified local angular sine series. -/
def angularFirst (s : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) : FormalRing.{u} :=
  (C (infSin (θ 0) (hθ 0)) + sineIncrement θ hθ 0) ^ 2 +
    (C (infSin (θ 1) (hθ 1)) + sineIncrement θ hθ 1) ^ 2 - C s

/-- The second relation in the verified local angular sine series. -/
def angularSecond (t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) : FormalRing.{u} :=
  (C (infSin (θ 0) (hθ 0)) + sineIncrement θ hθ 0) *
    (C (infSin (θ 1) (hθ 1)) + sineIncrement θ hθ 1) - C t

/-- The exact first equation is carried to its angular expression. -/
theorem sineCoordinateChange_first (s : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) :
    sineCoordinateChange θ hθ (polynomialFirst s θ hθ) = angularFirst s θ hθ := by
  simp only [polynomialFirst, angularFirst, map_sub, map_add, map_pow,
    sineCoordinateChange_C, sineCoordinateChange_X]

/-- The exact second equation is carried to its angular expression. -/
theorem sineCoordinateChange_second (t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) :
    sineCoordinateChange θ hθ (polynomialSecond t θ hθ) = angularSecond t θ hθ := by
  simp only [polynomialSecond, angularSecond, map_sub, map_add, map_mul,
    sineCoordinateChange_C, sineCoordinateChange_X]

/-- The defining ideal in the translated polynomial sine coordinates. -/
def polynomialIdeal (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) : Ideal FormalRing.{u} :=
  Ideal.span {polynomialFirst s θ hθ, polynomialSecond t θ hθ}

/-- The defining ideal in the local angular series coordinates. -/
def angularIdeal (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) : Ideal FormalRing.{u} :=
  Ideal.span {angularFirst s θ hθ, angularSecond t θ hθ}

/-- The formal coordinate change maps the full defining ideal, retaining its scheme structure. -/
theorem map_polynomialIdeal (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) :
    (polynomialIdeal s t θ hθ).map (sineCoordinateChange θ hθ).toRingHom =
      angularIdeal s t θ hθ := by
  simp only [polynomialIdeal, angularIdeal, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton]
  change Ideal.span {sineCoordinateChange θ hθ (polynomialFirst s θ hθ),
    sineCoordinateChange θ hθ (polynomialSecond t θ hθ)} = _
  rw [sineCoordinateChange_first, sineCoordinateChange_second]

/-- A genuine equivalence of formal quotient algebras, beyond the earlier bijection of points. -/
def formalQuotientEquiv (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) :
    (FormalRing.{u} ⧸ polynomialIdeal s t θ hθ) ≃ₐ[Surcomplex.{u}]
      FormalRing.{u} ⧸ angularIdeal s t θ hθ :=
  Ideal.quotientEquivAlg _ _ (sineCoordinateChange θ hθ) (map_polynomialIdeal s t θ hθ).symm

/-- The formal coordinate change preserves the native dimension of each quotient. -/
theorem formalQuotient_finrank_eq (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) :
    Module.finrank Surcomplex.{u} (FormalRing.{u} ⧸ polynomialIdeal s t θ hθ) =
      Module.finrank Surcomplex.{u} (FormalRing.{u} ⧸ angularIdeal s t θ hθ) :=
  (formalQuotientEquiv s t θ hθ).toLinearEquiv.finrank_eq

/-- At a solution both angular relations have zero constant term, as local equations must. -/
theorem angular_constant_terms_at_root (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    constantCoeff (angularFirst s θ hθ) = 0 ∧ constantCoeff (angularSecond t θ hθ) = 0 := by
  simpa only [angularFirst, angularSecond, map_sub, map_add, map_mul, map_pow,
    constantCoeff_C, constantCoeff_sineIncrement, add_zero, sub_eq_zero, Equations] using he

/-- After imposing the root equation, the first translated polynomial has
its exact linear and quadratic parts and no constant term. -/
theorem polynomialFirst_at_root (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    polynomialFirst s θ hθ = X 0 ^ 2 + X 1 ^ 2 +
      2 * C (infSin (θ 0) (hθ 0)) * X 0 + 2 * C (infSin (θ 1) (hθ 1)) * X 1 := by
  rw [polynomialFirst, ← he.1, map_add, map_pow, map_pow]
  ring

/-- The second translated polynomial is equally exact at every root. -/
theorem polynomialSecond_at_root (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    polynomialSecond t θ hθ = X 0 * X 1 +
      C (infSin (θ 0) (hθ 0)) * X 1 + C (infSin (θ 1) (hθ 1)) * X 0 := by
  rw [polynomialSecond, ← he.2, map_mul]
  ring

end
end Surreal.Surcomplex.CoupledAngular
