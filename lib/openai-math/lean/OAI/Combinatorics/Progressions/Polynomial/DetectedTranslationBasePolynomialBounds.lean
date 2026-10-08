/-
Modified for ProveIt: use MvPolynomial.coeff_add for the translated base
polynomial multiplication identity on Lean 4.32. All upstream statements
and quantitative bounds are unchanged.
-/
import OAI.Combinatorics.Progressions.Estimates.ControlledDetectedTranslationBaseBounds

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def detectedTranslationBasePolynomial
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) :
    VectorPolynomial σ ℝ (B → ℝ) :=
  ofCoordinates (Pi.basisFun ℝ B) (fun i =>
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial b ω hN (fun _ : σ => 1)
      (detectedTranslationBaseFunctional w d hw hwd M hM D i) g)

@[simp] theorem detectedTranslationBasePolynomial_coordinate
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (i : B) :
    coordinate (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) =
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial b ω hN (fun _ : σ => 1)
      (detectedTranslationBaseFunctional w d hw hwd M hM D i) g := by
  exact coordinate_ofCoordinates (Pi.basisFun ℝ B) _ i

@[simp] theorem detectedTranslationBasePolynomial_coefficients_apply
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (α : σ →₀ ℕ) (i : B) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) α i =
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial b ω hN (fun _ : σ => 1)
        (detectedTranslationBaseFunctional w d hw hwd M hM D i) g).coeff α := by
  rw [← detectedTranslationBasePolynomial_coordinate w d hw hwd M hM D b ω hN g i,
    coeff_coordinate]
  rfl

 theorem detectedTranslationBasePolynomial_coefficients
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (α : σ →₀ ℕ) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) α =
      realifyCoordinateMap (detectedTranslationBaseMap w d hw hwd M hM D)
        (coefficients ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.realGradedSymbolPolynomial b ω hN (fun _ : σ => 1) g.coord) α) := by
  funext i
  rw [detectedTranslationBasePolynomial_coefficients_apply,
    NilpotentLieFiltration.coeff_scalarSymbolPolynomial]
  rfl

 theorem detectedTranslationBasePolynomial_mul (hd : 1 ≤ d)
    (x y : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) :
    detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN (x * y) =
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN x +
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN y := by
  apply coefficients.injective
  ext α i
  simp only [map_add, Finsupp.add_apply, Pi.add_apply,
    detectedTranslationBasePolynomial_coefficients_apply]
  rw [(pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_mul b ω hN (fun _ : σ => 1)
    (detectedTranslationBaseFunctional w d hw hwd M hM D i)
    (detectedTranslationBaseFunctional_lie w d hw hwd M hM D i) hd,
    MvPolynomial.coeff_add]

 theorem detectedTranslationBasePolynomial_factorization (hd : 1 ≤ d)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hprod : E * P * Q = X) :
    detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X =
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E +
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P +
      detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q := by
  rw [← hprod, detectedTranslationBasePolynomial_mul w d hw hwd M hM D b ω hN hd,
    detectedTranslationBasePolynomial_mul w d hw hwd M hM D b ω hN hd]

 theorem detectedTranslationBasePolynomial_fast_coefficients_mem_span {J : Type*}
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded) (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : σ => 1) W)) (α : σ →₀ ℕ) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P) α ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  rw [detectedTranslationBasePolynomial_coefficients]
  exact realifyCoordinateMap_mem_span W.toSubmodule v hv _
    (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.mem_real_symbolPointwiseSubalgebra_iff_coefficients
      b ω hN (fun _ : σ => 1) W P.coord).mp hP α)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)

include hp hι hb

 theorem detectedTranslationBasePolynomial_slow_coefficients
    (T : σ → ℝ) (hT : ∀ a, 0 < T a)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound b ω hN (fun _ => 1) T (Real.exp p) E) :
    ∀ α i, |coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E) α i| ≤
      Real.exp ((p + 3)^3) / monomialScale T α := by
  intro α i
  rw [detectedTranslationBasePolynomial_coefficients_apply]
  exact detectedTranslationBase_slow_coefficients w d hw hwd M hM D b ω hN
    (fun _ => 1) T hT hp hι hb E hE i α

 theorem detectedTranslationBasePolynomial_exists_coefficient_grid
    (hB : (Fintype.card B : ℝ) ≤ p)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid b ω hN (fun _ => 1) m Q) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 3)^3) ∧
      ∀ α, coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q) α ∈
        realDenominatorGrid q := by
  obtain ⟨q, hq, hqb, hgrid⟩ := detectedTranslationBase_exists_common_coefficient_grid
    w d hw hwd M hM D b ω hN (fun _ => 1) hp hB hι hb m hm hmp Q hQ
  refine ⟨q, hq, hqb, ?_⟩
  exact coefficients_ofCoordinates_mem_realDenominatorGrid _ q hgrid

end Erdos3.PolynomialTranslationLie

end

end OAI
