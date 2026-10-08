/- Modified for ProveIt: supply the proved covered-chart measurable-open
instance explicitly in canonicalCoefficientDeckSample_jet_measurable, avoiding
Lean 4.32 instance-search timeout. The theorem statement is unchanged. -/
import OAI.Combinatorics.Progressions.Sampling.CoveredJetSampler

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K α : Type*} [Fintype K] [Fintype α] [DecidableEq α]
variable {m : ℕ} {J I Q O : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (Q j)] [∀ j, Fintype (O j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (dirs : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem canonicalCoefficientDeckSample_jet_measurable (d : ℕ) [NeZero d] :
    Measurable (fun p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) Q d =>
      euclideanCoefficientJetMap U root dirs rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)) := by
  let : OpensMeasurableSpace (CoveredJetChartSource U O Q n d) :=
    @BorelSpace.opensMeasurable _ _ _ (coveredJetChartSource_borel U d)
  have hchart := (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
    (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  have hjet := canonicalCoefficientJetArrays_measurable (I := I) (n := n) root dirs rows
  have hdeck : Measurable (coefficientDeckJetMap (B := Q) root dirs rows d) := measurable_of_finite _
  convert hchart.comp ((hjet.comp measurable_fst).prodMk (hdeck.comp measurable_snd)) using 1
  funext p
  exact canonicalCoefficientDeckSample_chart U o root dirs rows b hb bW d p.1 p.2

end Erdos3.VectorPolynomial

end

end OAI
