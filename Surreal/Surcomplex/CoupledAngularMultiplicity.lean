import Surreal.Algebra.FormalRectangle
import Surreal.Surcomplex.CoupledAngularFormalReduction
import Surreal.Surcomplex.CoupledAngularLocalAlgebra
import Surreal.Surcomplex.CoupledAngularReal

/-!
# Local and total multiplicities of the actual coupled angular equations

For `trigonometry:sec:coupled` and `trigonometry:eq:coupledroots`, multiplicity
is the native dimension of the formal quotient of the verified centered
angular equations. The quotient is finite and local; its dimension is one,
two or four on the corresponding collision strata. Summing over all actual
infinitesimal solutions gives total complex multiplicity four.
-/

universe u

namespace Surreal.Surcomplex.CoupledAngular

noncomputable section

/-- The formal local algebra at an actual infinitesimal angular center. -/
abbrev AngularAlgebra (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i)) := FormalRing.{u} ⧸ angularIdeal s t θ hθ

/-- The monomial quotient has the previously computed local-factor dimension. -/
theorem truncated_finrank (s t : Surcomplex.{u}) :
    Module.finrank Surcomplex.{u} (FormalRing.{u} ⧸ truncatedIdeal s t) =
      localFactorDimension s t := by
  change Module.finrank Surcomplex.{u}
    (FormalRectangle.Series ⧸ FormalRectangle.ideal (R := Surcomplex.{u})
      (FormalCoupled.localExponent (s + 2 * t)) (FormalCoupled.localExponent (s - 2 * t))) = _
  rw [FormalRectangle.quotient_finrank]
  unfold FormalCoupled.localExponent localFactorDimension
  split_ifs <;> rfl

/-- The formal angular quotient is finite-dimensional at every solution. -/
theorem angular_finite (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    Module.Finite Surcomplex.{u} (AngularAlgebra s t θ hθ) := by
  letI : Module.Finite Surcomplex.{u} (FormalRing.{u} ⧸ truncatedIdeal s t) :=
    FormalRectangle.quotient_finite _ _
  exact Module.Finite.equiv (truncatedAngularEquiv s t θ hθ he).toLinearEquiv

/-- Each angular intersection multiplicity equals the dimension of its algebraic local factor. -/
theorem angular_finrank (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    Module.finrank Surcomplex.{u} (AngularAlgebra s t θ hθ) = localFactorDimension s t := by
  rw [angular_finrank_eq_truncated s t θ hθ he, truncated_finrank]

/-- All local factors have positive dimension, including at a collision. -/
theorem localFactorDimension_pos (s t : Surcomplex.{u}) : 0 < localFactorDimension s t := by
  unfold localFactorDimension
  split_ifs <;> norm_num

/-- The formal quotient at a solution is a local ring, so its dimension is a local multiplicity. -/
theorem angular_isLocalRing (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    IsLocalRing (AngularAlgebra s t θ hθ) := by
  haveI : Nontrivial (AngularAlgebra s t θ hθ) :=
    Module.nontrivial_of_finrank_pos (R := Surcomplex.{u})
      (by rw [angular_finrank s t θ hθ he]; exact localFactorDimension_pos s t)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (angularIdeal s t θ hθ))
    Ideal.Quotient.mk_surjective

/-- Every root off both diagonal collisions has angular multiplicity one. -/
theorem angular_finrank_separated (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1)))
    (hp : s + 2 * t ≠ 0) (hq : s - 2 * t ≠ 0) :
    Module.finrank Surcomplex.{u} (AngularAlgebra s t θ hθ) = 1 := by
  simp [angular_finrank s t θ hθ he, localFactorDimension, hp, hq]

/-- A root on exactly one diagonal collision has angular multiplicity two. -/
theorem angular_finrank_single (s t : Surcomplex.{u}) (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations s t (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1)))
    (h : (s + 2 * t = 0 ∧ s - 2 * t ≠ 0) ∨
      (s + 2 * t ≠ 0 ∧ s - 2 * t = 0)) :
    Module.finrank Surcomplex.{u} (AngularAlgebra s t θ hθ) = 2 := by
  rw [angular_finrank s t θ hθ he, localFactorDimension_single s t h,
    FinitePolynomial.dualNumber_finrank]

/-- At the common collision the unique angular root has multiplicity four. -/
theorem angular_finrank_zero (θ : Fin 2 → Surcomplex.{u})
    (hθ : ∀ i, IsInfinitesimal (θ i))
    (he : Equations 0 0 (infSin (θ 0) (hθ 0)) (infSin (θ 1) (hθ 1))) :
    Module.finrank Surcomplex.{u} (AngularAlgebra 0 0 θ hθ) = 4 := by
  rw [angular_finrank 0 0 θ hθ he, localFactorDimension_zero, intersection_finrank]

/-- The actual angles of a solution, indexed for the formal coordinate construction. -/
def solutionCenter {s t : Surcomplex.{u}} (p : Solutions s t) : Fin 2 → Surcomplex.{u} :=
  ![p.1.1.1, p.1.2.1]

theorem infinitesimal_solutionCenter {s t : Surcomplex.{u}} (p : Solutions s t) :
    ∀ i, IsInfinitesimal (solutionCenter p i) := by
  intro i
  fin_cases i
  · exact p.1.1.2
  · exact p.1.2.2

/-- Angular multiplicity is defined by the native formal quotient dimension. -/
def angularMultiplicity {s t : Surcomplex.{u}} (p : Solutions s t) : ℕ :=
  Module.finrank Surcomplex.{u}
    (AngularAlgebra s t (solutionCenter p) (infinitesimal_solutionCenter p))

/-- Every support point on a fixed parameter stratum has the computed local dimension. -/
theorem angularMultiplicity_eq {s t : Surcomplex.{u}} (p : Solutions s t) :
    angularMultiplicity p = localFactorDimension s t :=
  angular_finrank s t (solutionCenter p) (infinitesimal_solutionCenter p) p.2

/-- The actual solution type is finite for all infinitesimal parameters. -/
theorem finite_solutions (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) : Finite (Solutions s t) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_solutions s t hs ht]
  split_ifs <;> norm_num

/-- Counting every actual root with its angular local multiplicity yields exactly four. -/
theorem total_angular_multiplicity (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) :
    letI := finite_solutions s t hs ht
    letI := Fintype.ofFinite (Solutions s t)
    ∑ p : Solutions s t, angularMultiplicity p = 4 := by
  classical
  letI := finite_solutions s t hs ht
  letI := Fintype.ofFinite (Solutions s t)
  simp only [angularMultiplicity_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  exact total_local_dimensions s t hs ht

/-- The local complex intersection multiplicity at a real angular root. -/
theorem angularMultiplicity_real (s t : Foundations.SignSequence.{u})
    (p : RealSolutions s t) :
    angularMultiplicity p.1 =
      (if s + 2 * t = 0 then 2 else 1) * (if s - 2 * t = 0 then 2 else 1) := by
  rw [angularMultiplicity_eq]
  have hp : ofReal s + 2 * ofReal t = ofReal (s + 2 * t) := by simp [map_ofNat]
  have hq : ofReal s - 2 * ofReal t = ofReal (s - 2 * t) := by simp [map_ofNat]
  simp only [localFactorDimension, hp, hq, map_eq_zero]

/-- The real locus carries total complex multiplicity four exactly when both
real diagonal parameters are nonnegative, and zero otherwise. -/
theorem total_real_angular_multiplicity (s t : Foundations.SignSequence.{u})
    (hs : Foundations.SignSequence.IsInfinitesimal s)
    (ht : Foundations.SignSequence.IsInfinitesimal t) :
    letI := finite_solutions (ofReal s) (ofReal t)
      ⟨hs, Foundations.SignSequence.infinitesimal_zero⟩
      ⟨ht, Foundations.SignSequence.infinitesimal_zero⟩
    letI := Fintype.ofFinite (RealSolutions s t)
    ∑ p : RealSolutions s t, angularMultiplicity p.1 =
      if 0 ≤ s + 2 * t ∧ 0 ≤ s - 2 * t then 4 else 0 := by
  classical
  letI := finite_solutions (ofReal s) (ofReal t)
    ⟨hs, Foundations.SignSequence.infinitesimal_zero⟩
    ⟨ht, Foundations.SignSequence.infinitesimal_zero⟩
  letI := Fintype.ofFinite (RealSolutions s t)
  simp only [angularMultiplicity_real, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_real_solutions s t hs ht]
  split_ifs <;> norm_num

end
end Surreal.Surcomplex.CoupledAngular
