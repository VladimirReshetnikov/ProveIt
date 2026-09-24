import Surreal.Algebra.DefinableSplitting
import Surreal.Algebra.ConstantTermPrenex
import Surreal.HahnSeries.ConstantTermGraph
import Surreal.HahnSeries.IntersectiveDetector

/-!
# Definable splittings and quantified graphs in Hahn pullbacks

The full Hahn-ring scope of `odg:def:cor:splitting` and
`odg:def:rem:sigma2`, keeping the ordinary coefficient output explicit.
-/

namespace Surreal.HahnSeries

open ConstantTermGraph

noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CommRing O]

/-- Graph and kernel formulas give the exact definable splitting of a full Hahn pullback. -/
theorem coefficientRestricted_definableSplitting (i : O →+* K) (hi : Function.Injective i)
    (hgraph : ∀ x n : coefficientRestrictedSubring (Γ := Γ) i,
      Graph x n ↔ n = coefficientRestrictedConstants i (coefficientRestrictedRetraction i hi x))
    (hkernel : ∀ a : coefficientRestrictedSubring (Γ := Γ) i,
      a.val ∈ purelyInfiniteIdeal ↔ ∃ y, a ^ 2 = 2 * y ^ 2) :
    DefinableSplitting (coefficientRestrictedRetraction (Γ := Γ) i hi)
      (coefficientRestrictedConstants i) := by
  refine definableSplitting_of_graph _ _ ?_ hgraph ?_
  · exact CoefficientPullback.retraction_sectionMap (nonpositiveConstantCoeff (Γ := Γ) (R := K))
      i hi nonpositiveConstants nonpositiveConstantCoeff_constants
  · intro a
    exact (hkernel a).symm.trans
      (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi a).symm

/-- Integer pullbacks over any characteristic-zero field containing sqrt(2). -/
theorem integerRestricted_definableSplitting [CharZero K] (r : K) (hr : r ^ 2 = 2) :
    DefinableSplitting (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom K)
      Int.cast_injective) (coefficientRestrictedConstants (Int.castRingHom K)) :=
  coefficientRestricted_definableSplitting _ Int.cast_injective
    (integerRestricted_constantTermGraph_iff r hr) (integerRestricted_purelyInfinite_iff_quadratic r hr)

/-- Gaussian pullbacks over any characteristic-zero field containing sqrt(2). -/
theorem gaussianRestricted_definableSplitting [CharZero K]
    (i : GaussianInt →+* K) (hi : Function.Injective i) (r : K) (hr : r ^ 2 = 2) :
    DefinableSplitting (coefficientRestrictedRetraction (Γ := Γ) i hi)
      (coefficientRestrictedConstants i) :=
  coefficientRestricted_definableSplitting i hi (gaussianRestricted_constantTermGraph_iff i hi r hr)
    (gaussianRestricted_purelyInfinite_iff_quadratic i hi r hr)

/-- The real Hahn splitting in the source, with no extra coefficient-field assumptions. -/
theorem realRestricted_definableSplitting :
    DefinableSplitting (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom ℝ)
      Int.cast_injective) (coefficientRestrictedConstants (Int.castRingHom ℝ)) :=
  integerRestricted_definableSplitting (Real.sqrt 2) (by norm_num [Real.sq_sqrt])

/-- The complex Hahn splitting in the source, with ordinary Gaussian output. -/
theorem complexRestricted_definableSplitting :
    DefinableSplitting (coefficientRestrictedRetraction (Γ := Γ) GaussianInt.toComplex
      GaussianInt.toComplex_injective) (coefficientRestrictedConstants GaussianInt.toComplex) := by
  apply gaussianRestricted_definableSplitting GaussianInt.toComplex GaussianInt.toComplex_injective
    (Real.sqrt 2 : ℂ)
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- Both quantifier orders give the ordinary coefficient output whenever the detector holds. -/
theorem coefficientRestricted_prenexGraph_iff (i : O →+* K) (hi : Function.Injective i)
    (hSplit : DefinableSplitting (coefficientRestrictedRetraction (Γ := Γ) i hi)
      (coefficientRestrictedConstants i))
    (hdet : ∀ a : coefficientRestrictedSubring (Γ := Γ) i,
      IntersectivePolynomial.Detects a ↔ nonpositiveConstantCoeff a.val ≠ 0)
    (a c : coefficientRestrictedSubring (Γ := Γ) i) :
    (UniversalGraph a c ↔ c = coefficientRestrictedConstants i
      (coefficientRestrictedRetraction i hi a)) ∧
      (ExistsForallGraph a c ↔ c = coefficientRestrictedConstants i
        (coefficientRestrictedRetraction i hi a)) ∧
      (ForallExistsGraph a c ↔ c = coefficientRestrictedConstants i
        (coefficientRestrictedRetraction i hi a)) := by
  have hd (x : coefficientRestrictedSubring (Γ := Γ) i) :
      IntersectivePolynomial.Detects x ↔ coefficientRestrictedRetraction i hi x ≠ 0 :=
    (hdet x).trans (not_congr (CoefficientPullback.mem_ker_iff
      (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi x)).symm
  obtain ⟨h₁, h₂, h₃⟩ := prenex_graph_equivalences
    (coefficientRestrictedRetraction (Γ := Γ) i hi) hd hSplit.kernel_formula a c
  have hg := hSplit.retraction_formula a c
  exact ⟨h₁.trans hg, h₂.trans hg, h₃.trans hg⟩

/-- Both printed prenex forms are correct in the full real Hahn pullback. -/
theorem realRestricted_prenexGraph_iff
    (a c : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ)) :
    (UniversalGraph a c ↔ c = coefficientRestrictedConstants (Int.castRingHom ℝ)
      (coefficientRestrictedRetraction (Int.castRingHom ℝ) Int.cast_injective a)) ∧
      (ExistsForallGraph a c ↔ c = coefficientRestrictedConstants (Int.castRingHom ℝ)
        (coefficientRestrictedRetraction (Int.castRingHom ℝ) Int.cast_injective a)) ∧
      (ForallExistsGraph a c ↔ c = coefficientRestrictedConstants (Int.castRingHom ℝ)
        (coefficientRestrictedRetraction (Int.castRingHom ℝ) Int.cast_injective a)) :=
  coefficientRestricted_prenexGraph_iff _ Int.cast_injective
    realRestricted_definableSplitting realRestricted_detector_iff a c

/-- Both printed prenex forms are correct in the full Gaussian Hahn pullback. -/
theorem complexRestricted_prenexGraph_iff
    (a c : coefficientRestrictedSubring (Γ := Γ) GaussianInt.toComplex) :
    (UniversalGraph a c ↔ c = coefficientRestrictedConstants GaussianInt.toComplex
      (coefficientRestrictedRetraction GaussianInt.toComplex GaussianInt.toComplex_injective a)) ∧
      (ExistsForallGraph a c ↔ c = coefficientRestrictedConstants GaussianInt.toComplex
        (coefficientRestrictedRetraction GaussianInt.toComplex GaussianInt.toComplex_injective a)) ∧
      (ForallExistsGraph a c ↔ c = coefficientRestrictedConstants GaussianInt.toComplex
        (coefficientRestrictedRetraction GaussianInt.toComplex GaussianInt.toComplex_injective a)) :=
  coefficientRestricted_prenexGraph_iff GaussianInt.toComplex GaussianInt.toComplex_injective
    complexRestricted_definableSplitting complexRestricted_detector_iff a c

end
end Surreal.HahnSeries
