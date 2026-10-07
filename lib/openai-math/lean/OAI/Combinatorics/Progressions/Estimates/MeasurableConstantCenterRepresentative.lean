/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedFiberCap
import OAI.Combinatorics.Progressions.Lattices.LatticeMeasurableRepresentative

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem exists_measurable_coefficient_representative_of_layers
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    (hsection : ∀ j, ∃ r : (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) →
        euclideanSubspace (U j), Measurable r ∧
        ∀ x, QuotientAddGroup.mk' _ (r x) = x) :
    ∃ r : CoefficientTorus (K := K) U → CoefficientArray (K := K) U,
      Measurable r ∧ ∀ x, QuotientAddGroup.mk' (coefficientIntegerLattice U) (r x) = x := by
  classical
  choose r hr hright using hsection
  let f : CoefficientTorus (K := K) U → CoefficientArray (K := K) U :=
    fun x s => euclideanSubspaceArrayEquiv (U s.1)
      (r s.1 (euclideanCoefficientEquiv U x s.1 s.2)) ()
  refine ⟨f, ?_, ?_⟩
  · apply Measurable.of_eval
    intro s
    exact (measurable_pi_apply ()).comp
      ((euclideanSubspaceArrayEquiv (U s.1)).continuous.measurable.comp
        ((hr s.1).comp ((measurable_pi_apply s.2).comp
          ((measurable_pi_apply s.1).comp
            (euclideanCoefficientEquiv_continuous U).measurable))))
  · intro x
    apply coefficientCoordinateTorus_injective U
    funext s
    rw [coefficientCoordinateTorus_mk]
    have hunit : (fun _ : Unit => f x s) = euclideanSubspaceArrayEquiv (U s.1)
        (r s.1 (euclideanCoefficientEquiv U x s.1 s.2)) := by
      funext a
      cases a
      rfl
    rw [hunit, ← euclideanSubspaceTorusEquiv_mk, hright]
    exact (euclideanSubspaceTorusEquiv (U s.1)).apply_symm_apply _

theorem exists_measurable_subtractive_constant_center_of_representative
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := Empty) U)]
    [BorelSpace (CoefficientTorus (K := Empty) U)]
    (r : CoefficientTorus (K := Empty) U → CoefficientArray (K := Empty) U)
    (hr : Measurable r)
    (hright : ∀ x, QuotientAddGroup.mk' (coefficientIntegerLattice U) (r x) = x) :
    ∃ c : CoefficientTorus (K := K) U → ∀ j, U j, Measurable c ∧
      ∀ x, coefficientConstantCenter U x =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray (K := K) U (fun s => c x s.1))) := by
  let v : CoefficientTorus (K := K) U → CoefficientArray (K := Empty) U :=
    fun x => r (-(coefficientEvaluationTorus U 0 x))
  let c : CoefficientTorus (K := K) U → ∀ j, U j :=
    fun x j => v x ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩
  refine ⟨c, ?_, ?_⟩
  · apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply _).comp
      (hr.comp (coefficientEvaluationTorus_continuous U 0).neg.measurable)
  · intro x
    have hc : (fun s : CoefficientSlot Empty m => c x s.1) = v x := by
      funext s
      rcases s with ⟨j,d⟩
      rw [emptyCoefficientExponent_eq (j.val + 1) d]
    rw [← constantCoefficientTorusMap_mk, hc]
    change coefficientConstantCenter U x = -(constantCoefficientTorusMap U
      (QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (r (-(coefficientEvaluationTorus U 0 x)))))
    rw [hright, map_neg, neg_neg]
    rfl

theorem exists_measurable_subtractive_constant_center
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (bW : ∀ j, Basis (B j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    ∃ c : CoefficientTorus (K := K) U → ∀ j, U j, Measurable c ∧
      ∀ x, coefficientConstantCenter U x =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray (K := K) U (fun s => c x s.1))) := by
  let : MeasurableSpace (CoefficientTorus (K := Empty) U) := borel _
  let : BorelSpace (CoefficientTorus (K := Empty) U) := ⟨rfl⟩
  obtain ⟨r, hr, hright⟩ := exists_measurable_coefficient_representative_of_layers
    (K := Empty) U (fun j => lattice_exists_measurable_representative
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))) (bW j))
  exact exists_measurable_subtractive_constant_center_of_representative U r hr hright

end Erdos3.VectorPolynomial

end

end OAI
