/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.CoveredJetReference
import OAI.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage
import OAI.Combinatorics.Progressions.Probability.CoefficientDeckDensityLawCongruence

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical Matrix

theorem mixedArrayIntegerImage_measurable {I Z J O : Type*} [Fintype J]
    (A : Matrix O J ℤ) :
    Measurable (mixedArrayIntegerImage (I := I) (Z := Z) A) := by
  unfold mixedArrayIntegerImage Matrix.mulVec dotProduct
  fun_prop

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedCoveredJetCoordinates (d : ℕ)
    (p : (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) : CoveredJetChartSource U O B n d :=
  fun j t => (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (p.1 j) t), p.2 j t)

theorem mixedCoveredJetCoordinates_measurable (d : ℕ) :
    Measurable (mixedCoveredJetCoordinates (O := O) (B := B) (n := n) U o d) := by
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro t
  exact ((orthonormalMixedChart (o j)).measurable.comp
    (((measurable_pi_apply t).comp (mixedArrayRegroup _ _ _).measurable).comp
      ((measurable_pi_apply j).comp measurable_fst))).prodMk
    ((measurable_pi_apply t).comp ((measurable_pi_apply j).comp measurable_snd))

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (I j)] [Fintype α] in
theorem canonicalCoefficientJetArrays_measurable :
    Measurable (canonicalCoefficientJetArrays (I := I) (n := n) root A rows) := by
  apply Measurable.of_eval
  intro j
  exact (mixedArrayIntegerImage_measurable
    (boundedCoefficientJetMatrix root A (j.val + 1) (rows j))).comp (measurable_pi_apply j)

variable [∀ j, Fintype (B j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem canonicalCoefficientDeckSample_chart (d : ℕ) [NeZero d]
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    euclideanCoefficientJetMap U root A rows
      (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x r) =
    coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d
      (canonicalCoefficientJetArrays root A rows x, coefficientDeckJetMap root A rows d r)) := by
  funext j t
  exact canonicalCoefficientDeckSample_mixed_jets U b hb o root A rows bW d
    (Nat.pos_of_ne_zero (NeZero.ne d)) x r j t

variable [∀ j, Fintype (O j)]

theorem canonicalCoefficientDeckSample_jet_law (d : ℕ) [NeZero d]
    (ρ : Measure (CoefficientSamplerArrays (K := K) I n)) [SFinite ρ] :
    (ρ.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
      (fun p => euclideanCoefficientJetMap U root A rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)) =
    (realDensityMeasure
      ((ρ.map (canonicalCoefficientJetArrays root A rows)).prod
        (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure)
      (fun p => coefficientDeckJetDensity root A rows d p.2)).map
        (fun p => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d p)) := by
  have hF := canonicalCoefficientJetArrays_measurable (I := I) (n := n) root A rows
  have hR : Measurable (coefficientDeckJetMap (B := B) root A rows d) := measurable_of_finite _
  have hφ : Measurable (fun p => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d p)) :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := B) (n := n) U o d)
  rw [← realDensityMeasure_prod_right _ _ _ (measurable_of_finite _),
    ← coefficientDeckJetDensity_law]
  rw [← PMF.toMeasure_map _ _ hR, Measure.map_prod_map _ _ hF hR,
    Measure.map_map hφ (hF.prodMap hR)]
  congr 1
  funext p
  exact canonicalCoefficientDeckSample_chart U o root A rows b hb bW d p.1 p.2

end VectorPolynomial

end Erdos3

end

end OAI
