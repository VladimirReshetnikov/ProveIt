import OAI.Combinatorics.Progressions.Probability.ScaledArrayLaw

namespace OAI

section

namespace Erdos3

open Module Submodule Set
open scoped BigOperators

def mixedArraySupported {I Z J : Type*} [Fintype I] [Fintype Z]
    (c w : I → J → ℝ) (p : Z → J → PMF ℤ) (x : (I → J → ℝ) × (Z → J → ℤ)) : Prop :=
  ∀ j, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun z => p z j)
    (mixedArrayRegroup I Z J x j) ≠ 0

theorem mixedArraySupported_iff_rows {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (p : Z → J → PMF ℤ) (x : (I → J → ℝ) × (Z → J → ℤ)) :
    mixedArraySupported c w p x ↔
      (∀ i, affineProductProfile (c i) (w i) (x.1 i) ≠ 0) ∧
      (∀ z j, x.2 z j ∈ (p z j).support) := by
  classical
  constructor
  · intro hx
    have hs (j) := (mixedCoefficientDensity_support (fun i => c i j) (fun i => w i j)
      (fun z => p z j) (mixedArrayRegroup I Z J x j)).mp (hx j)
    refine ⟨?_, fun z j => (hs j).2 z⟩
    intro i
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact (hs j).1 i
  · rintro ⟨hc, hp⟩ j
    apply (mixedCoefficientDensity_support _ _ _ _).mpr
    refine ⟨?_, fun z => hp z j⟩
    intro i
    exact (Finset.prod_ne_zero_iff.mp (hc i)) j (Finset.mem_univ j)

def mixedArrayInChart {D I J : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (o : OrthonormalBasis I ℝ W) (x : (I → J → ℝ) × (Fin n → J → ℤ)) : Prop :=
  ∀ j, normalizedLatticePoint W b (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) ∈
    standardLatticeSmallBox D

theorem mixedArrayQuotient_injOn_chart {D I J : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W) :
    Set.InjOn (mixedArrayQuotient (J := J) W b hb o) {x | mixedArrayInChart W b o x} := by
  intro x hx y hy he
  apply (mixedArrayRegroup I (Fin n) J).injective
  funext j
  apply (orthonormalMixedChart o).injective
  exact normalizedLatticeQuotient_injOn W b hb (Subset.rfl) (hx j) (hy j) (congrFun he j)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem mixedScalarArrayLaw_support {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    ∀ᵐ x ∂mixedScalarArrayLaw c w p, mixedArraySupported c w p x := by
  let μ := fun j => mixedCoefficientLaw (fun i => c i j) (fun i => w i j) (fun z => p z j)
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    mixedCoefficientLaw_probability _ _ (fun i => hw i j) _
  have h (j) : ∀ᵐ x ∂μ j,
      mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun z => p z j) x ≠ 0 := by
    dsimp only [μ]
    rw [mixedCoefficientLaw_density _ _ (fun i => hw i j)]
    apply realDensityMeasure_ae_of_support
    · exact ((affineProductProfile_contDiff (fun i => c i j)
        (fun i => w i j)).continuous.measurable.comp measurable_fst).mul
        ((measurable_of_countable (fun z : Z → ℤ => ∏ i, (p i j (z i)).toReal)).comp measurable_snd)
    · exact fun _ hx => hx
  have hall : ∀ᵐ x ∂Measure.pi μ, ∀ j,
      mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun z => p z j) (x j) ≠ 0 :=
    ae_all_iff.mpr (fun j => (Measure.quasiMeasurePreserving_eval μ j).ae (h j))
  rw [show Measure.pi μ = (mixedScalarArrayLaw c w p).map (mixedArrayRegroup I Z J) from
    (mixedScalarArrayLaw_regroup c w hw p).symm] at hall
  exact ae_of_ae_map (mixedArrayRegroup I Z J).measurable.aemeasurable hall

end Erdos3

end

end OAI
