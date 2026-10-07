import OAI.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop
import OAI.Combinatorics.Progressions.Polynomial.ProductPolynomialMaps

namespace OAI

universe sourceLevel

section

namespace Erdos3.RationalFilteredNilmanifold
open Module
variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

 theorem productProjection_repr (x : ∀ i, L i) (i : ι) (j : Fin (d i)) :
    (D i).basis.repr (x i) j =
      (pi D).basis.repr x (Fintype.equivFin (Σ i, Fin (d i)) ⟨i, j⟩) := by
  change _ = (productFinBasis D).repr x _
  rw [productFinBasis, Basis.repr_reindex_apply]
  simp only [Equiv.symm_apply_apply, Pi.basis_repr]

 theorem productProjection_coordinate_logHeight {p : ℝ} (x : ∀ i, L i)
    (hx : ∀ k, rationalLogHeight ((pi D).basis.repr x k) ≤ p) (i : ι) (j : Fin (d i)) :
    rationalLogHeight ((D i).basis.repr (x i) j) ≤ p := by
  rw [productProjection_repr D x i j]
  exact hx _

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module
variable {L M : Type sourceLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}

 theorem pairFirstProjection_filtered (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e) (j : ℕ)
    (x : PairAlgebra L M) (hx : x ∈ (pi (pairModels D E)).filtration.layer j) :
    liePiEval (R := ℚ) true x ∈ D.filtration.layer j :=
  (NilpotentLieFiltration.mem_pi_layer (fun i => (pairModels D E i).filtration) j x).mp hx true

 theorem pairFrequency_zero_comp (η : L →ₗ[ℚ] ℚ) :
    pairFrequency η (0 : M →ₗ[ℚ] ℚ) =
      η.comp (liePiEval (R := ℚ) (M := BoolLieFamily L M) true).toLinearMap := by
  apply LinearMap.ext
  intro x
  change pairFrequency η (0 : M →ₗ[ℚ] ℚ) x = η (x true)
  rw [pairFrequency_apply]
  exact add_zero _

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold
variable {σ L : Type} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] {e : ℕ}
    (D : RationalFilteredNilmanifold L d e)

theorem pairTranslationProjection_coordinate_logHeight {p : ℝ}
    (x : PairAlgebra (weightedSubalgebra w d) L)
    (hx : ∀ j, rationalLogHeight
      ((pi (pairModels (weightedTranslationNilmanifold w d hw hwd) D)).basis.repr x j) ≤ p)
    (i : WeightedBasisIndex w d) :
    rationalLogHeight ((weightedBasis w d hw).repr (x true) i) ≤ p := by
  have h := productProjection_coordinate_logHeight
    (pairModels (weightedTranslationNilmanifold w d hw hwd) D) x hx true
    (weightedIndexOrder w d i)
  change rationalLogHeight ((weightedOrderedBasis w d hw).repr (x true)
    (weightedIndexOrder w d i)) ≤ p at h
  have he := weightedOrderedBasis_repr w d hw (x true) (weightedIndexOrder w d i)
  have he' : (weightedOrderedBasis w d hw).repr (x true) (weightedIndexOrder w d i) =
      (weightedBasis w d hw).repr (x true) i :=
    he.trans (congrArg ((weightedBasis w d hw).repr (x true)) ((weightedIndexOrder w d).symm_apply_apply i))
  exact he' ▸ h

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial
open scoped TensorProduct

variable {L M : Type sourceLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ ι κ : Type*} (w : σ → ℕ)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels D E)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hG : ∀ j, D.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem pairOrbit_first_projection_log
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
      (M := BoolLieFamily L M) true)).toLinearMap.restrictScalars ℚ) (pairOrbit D E p q).log = p.log := by
  let g : ∀ i : Bool, (pairModels D E i).filtration.realification.PolynomialOrbit w :=
    fun i => by cases i; exact q; exact p
  have h := NilpotentLieFiltration.piRealOrbit_projection_log
    (fun i => (pairModels D E i).filtration) g true
  change VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
      (M := BoolLieFamily L M) true)).toLinearMap.restrictScalars ℚ) (pairOrbit D E p q).log = p.log at h
  exact h

theorem pairOrbitSymbol_first_projection
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    realificationLieHom
      ((pi (pairModels D E)).filtration.filteredPolynomialSymbolMap D.filtration
        (liePiEval (R := ℚ) true) (pairFirstProjection_filtered D E) w)
      (pairOrbitSymbol D E p q b ω hF).coord =
        D.filtration.realSymbolOfPolynomial c ν hG w p.log := by
  have h := (pi (pairModels D E)).filtration.realFilteredPolynomialSymbolMap_polynomial
    D.filtration (liePiEval (R := ℚ) true) (pairFirstProjection_filtered D E)
    b ω hF c ν hG w ⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩
  change realificationLieHom
      ((pi (pairModels D E)).filtration.filteredPolynomialSymbolMap D.filtration
        (liePiEval (R := ℚ) true) (pairFirstProjection_filtered D E) w)
      (pairOrbitSymbol D E p q b ω hF).coord =
    D.filtration.realSymbolOfPolynomial c ν hG w
      (VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
        (M := BoolLieFamily L M) true)).toLinearMap.restrictScalars ℚ) (pairOrbit D E p q).log) at h
  refine h.trans (congrArg (D.filtration.realSymbolOfPolynomial c ν hG w) ?_)
  exact pairOrbit_first_projection_log D E w p q

end Erdos3.RationalFilteredNilmanifold

end

end OAI
