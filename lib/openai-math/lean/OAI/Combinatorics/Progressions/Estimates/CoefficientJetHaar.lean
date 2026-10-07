import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OAI.Combinatorics.Progressions.Fourier.EuclideanJetTorus

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientBooleanJetTorusMap_measurePreserving {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus (O j) (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus (O j) (U j))]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (SubspaceArrayTorus (O j) (U j)))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (coefficientBooleanJetTorusMap U root D rows) μ (Measure.pi ν) := by
  have hc := coefficientBooleanJetTorusMap_continuous U root D rows
  have hs := coefficientBooleanJetTorusMap_surjective U root D a ha hperiod rows hinj hdegree
  let _ : CompactSpace (BooleanJetTorus O U) := by
    have h := isCompact_univ.image hc
    rw [Set.image_univ, Set.range_eq_univ.mpr hs] at h
    exact ⟨h⟩
  let _ : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let _ : (Measure.pi ν).IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := Measure.pi ν) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving hc hs (by simp)

theorem coefficientSiteImage_booleanJet_haar {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset α) U)] [BorelSpace (SiteTorus (Finset α) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus (O j) (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus (O j) (U j))]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (SubspaceArrayTorus (O j) (U j)))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    (μ.map (Set.rangeFactorization E)).map
      (fun y : Set.range E => siteBooleanJetTorusMap U rows y.val) = Measure.pi ν := by
  intro E
  have hc := (siteBooleanJetTorusMap_continuous U rows).comp
    (continuous_subtype_val : Continuous (Subtype.val : Set.range E → SiteTorus (Finset α) U))
  have hπ : Measurable (Set.rangeFactorization E) :=
    (coefficientSiteTorusMap_continuous U (integerAffineCube root D)).rangeFactorization.measurable
  have hκ : Measurable (fun y : Set.range E => siteBooleanJetTorusMap U rows y.val) := hc.measurable
  exact (Measure.map_map hκ hπ).trans
    (coefficientBooleanJetTorusMap_measurePreserving U root D a ha hperiod rows hinj hdegree μ ν).map_eq

end Erdos3.VectorPolynomial

end

end OAI
