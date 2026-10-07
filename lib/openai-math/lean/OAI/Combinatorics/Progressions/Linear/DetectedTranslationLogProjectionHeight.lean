import OAI.Combinatorics.Progressions.Estimates.DetectedTranslationNormalizedLogBounds
import OAI.Combinatorics.Progressions.Sampling.WeightedTranslationProjectionGridBudget

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)

theorem detectedTranslationLogProjectionMatrix_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (k : WeightedBasisIndex w d) (i : ι) :
    rationalLogHeight (detectedTranslationLogProjectionMatrix w d hw b ω k i) ≤ p := by
  unfold detectedTranslationLogProjectionMatrix
  split_ifs
  · exact pairResidueTranslationProjection_coordinate_logHeight w d hw hwd M hM D
      (b i) (hb i) k
  · simpa [rationalLogHeight] using hp

theorem detectedTranslationLogProjectionMatrix_height_of_basis {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (k : WeightedBasisIndex w d) (i : ι) :
    RationalHeightLE (detectedTranslationLogProjectionMatrix w d hw b ω k i) ⌈Real.exp p⌉₊ :=
  rationalHeightLE_ceil_exp
    (detectedTranslationLogProjectionMatrix_logHeight w d hw hwd M hM D b ω hp hb k i)

variable (hN : ∀ j,
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_detectedTranslationLogCoordinate_grid_of_basis_height [Fintype ι]
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (m : ℕ) (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧
      q ≤ ⌈Real.exp p⌉₊ ^ (Fintype.card (WeightedBasisIndex w d) * Fintype.card ι) * m ∧
      ∀ E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1),
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
          b ω hN (fun _ : U => 1) m E →
        ∀ k, realPolynomialCoefficientGrid q
          (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) :=
  exists_detectedTranslationLogCoordinate_common_grid w d hw hwd M hM D b ω hN
    (detectedTranslationLogProjectionMatrix_height_of_basis w d hw hwd M hM D b ω hp hb) m hm

theorem detectedTranslationLogCoordinate_normalized_mass_of_basis_height [Fintype U] [Fintype ι]
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) (k : WeightedBasisIndex w d) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) ≤
        ((Fintype.card U : ℝ) + 1) ^ d *
          ((Fintype.card ι : ℝ) * (⌈Real.exp p⌉₊ : ℝ) * A) :=
  detectedTranslationLogCoordinate_normalized_mass w d hw hwd M hM D b ω hN
    T hT hA (Nat.cast_nonneg _) k
    (fun i => (detectedTranslationLogProjectionMatrix_height_of_basis
      w d hw hwd M hM D b ω hp hb k i).abs_real_le) E hE

theorem exists_detectedTranslationLogCoordinate_exp_grid_of_basis_height [Fintype ι]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 3) ^ 3) ∧
      ∀ E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1),
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
          b ω hN (fun _ : U => 1) m E →
        ∀ k, realPolynomialCoefficientGrid q
          (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) := by
  obtain ⟨q, hq, hbound, hgrid⟩ :=
    exists_detectedTranslationLogCoordinate_grid_of_basis_height
      w d hw hwd M hM D b ω hN hp hb m hm
  refine ⟨q, hq, ?_, hgrid⟩
  apply detectedTranslationCoordinate_denominator_le_exp
    (Fintype.card (WeightedBasisIndex w d)) (Fintype.card ι) m q hp _ hι hmp hbound
  exact (Nat.cast_le.mpr (weightedBasisIndex_card_le_pair_basis w d hw b)).trans hι

theorem detectedTranslationLogCoordinate_normalized_mass_exp_of_basis_height
    [Fintype U] [Fintype ι] {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (T : U → ℝ) (hT : ∀ i, 0 < T i)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T (Real.exp p) E) (k : WeightedBasisIndex w d) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) ≤
        ((Fintype.card U : ℝ) + 1) ^ d * Real.exp ((p + 3) ^ 3) := by
  apply (detectedTranslationLogCoordinate_normalized_mass_of_basis_height
    w d hw hwd M hM D b ω hN hp hb T hT (Real.exp_nonneg p) E hE k).trans
  exact mul_le_mul_of_nonneg_left
    (detectedTranslationCoordinate_slow_factor_le_exp (Fintype.card ι) hp hι) (by positivity)

end Erdos3.PolynomialTranslationLie

end

end OAI
