/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.MvPolynomial.Funext
import OAI.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationIdentity
import OAI.Combinatorics.Progressions.Polynomial.TranslationLogCoordinatePolynomials

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realSymbolCoordinate (x : F.RealPolynomialSymbol w) (i : ι) :
    MvPolynomial σ ℝ :=
  coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom
    (F.realSymbolRepresentative b ω hlayers w x)

@[simp] theorem coeff_realSymbolCoordinate (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) :
    (F.realSymbolCoordinate b ω hlayers w x i).coeff α =
      (b.baseChange ℝ).repr
        (coefficients (F.realSymbolRepresentative b ω hlayers w x) α) i := by
  simp only [realSymbolCoordinate, coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    Basis.coord_apply]

theorem realSymbolCoordinate_coeff_of_ne (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α ≠ ω i) :
    (F.realSymbolCoordinate b ω hlayers w x i).coeff α = 0 := by
  rw [F.coeff_realSymbolCoordinate]
  exact F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w x α i h

@[simp] theorem realSymbolCoordinate_coeff_symbol (x : F.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w ω) :
    (F.realSymbolCoordinate b ω hlayers w x z.val.2).coeff z.val.1 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z := by
  rw [F.coeff_realSymbolCoordinate]
  exact F.realSymbolRepresentative_coefficient b ω hlayers w x z

theorem realSymbolCoordinate_isWeightedHomogeneous (x : F.RealPolynomialSymbol w)
    (i : ι) :
    (F.realSymbolCoordinate b ω hlayers w x i).IsWeightedHomogeneous w (ω i) := by
  intro α hα
  by_contra h
  exact hα (F.realSymbolCoordinate_coeff_of_ne b ω hlayers w x α i h)

@[simp] theorem realSymbolCoordinate_coeff_zero (x : F.RealPolynomialSymbol w) (i : ι) :
    (F.realSymbolCoordinate b ω hlayers w x i).coeff 0 = 0 := by
  rw [F.coeff_realSymbolCoordinate, F.realSymbolRepresentative_constant b ω hlayers w x,
    map_zero, Finsupp.zero_apply]

@[simp] theorem realSymbolCoordinate_constantCoeff (x : F.RealPolynomialSymbol w) (i : ι) :
    MvPolynomial.constantCoeff (F.realSymbolCoordinate b ω hlayers w x i) = 0 := by
  exact F.realSymbolCoordinate_coeff_zero b ω hlayers w x i

theorem realSymbolCoordinate_slow_coefficients (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hlayers w T M g)
    (α : σ →₀ ℕ) (i : ι) :
    |(F.realSymbolCoordinate b ω hlayers w g.coord i).coeff α| ≤
      M / monomialScale T α := by
  rw [F.coeff_realSymbolCoordinate]
  exact F.realSymbolRepresentative_slow_coefficients b ω hlayers w T hT hM g hg α i

theorem realSymbolCoordinate_rational_coefficients (l : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hlayers w l g) :
    (fun z : (σ →₀ ℕ) × ι =>
      (F.realSymbolCoordinate b ω hlayers w g.coord z.2).coeff z.1)
        ∈ realDenominatorGrid l := by
  simpa only [F.coeff_realSymbolCoordinate] using
    F.realSymbolRepresentative_rational_coefficients b ω hlayers w l g hg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

noncomputable def nativeTranslationLogCoordinate (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) (k : κ) :
    MvPolynomial U ℝ :=
  VectorPolynomial.coordinate ((b.baseChange ℝ).coord k).toAddMonoidHom p

omit [Fintype κ] in
@[simp] theorem nativeTranslationLogCoordinate_coeff (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d))
    (k : κ) (α : U →₀ ℕ) :
    (nativeTranslationLogCoordinate w d b p k).coeff α =
      (b.baseChange ℝ).repr (VectorPolynomial.coefficients p α) k :=
  VectorPolynomial.coeff_coordinate _ _ _

theorem nativeTranslationLogCoordinate_eval (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) (u : U → ℝ) :
    VectorPolynomial.eval₂ u p =
      ∑ k, (eval u (nativeTranslationLogCoordinate w d b p k)) ⊗ₜ[ℚ] b k := by
  calc
    VectorPolynomial.eval₂ u p =
        ∑ k, (b.baseChange ℝ).repr (VectorPolynomial.eval₂ u p) k •
          (b.baseChange ℝ) k := ((b.baseChange ℝ).sum_repr _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      change ((b.baseChange ℝ).coord k) (VectorPolynomial.eval₂ u p) •
        (b.baseChange ℝ) k = _
      rw [VectorPolynomial.coordinate_eval₂, Basis.baseChange_apply]
      simp only [nativeTranslationLogCoordinate, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

noncomputable def nativeTranslationGroupPolynomial (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) :
    PolynomialTranslationGroupOver (MvPolynomial U ℝ) B :=
  translationLogGroupPolynomial w d b (nativeTranslationLogCoordinate w d b p)

theorem nativeTranslationGroupPolynomial_specialize (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u) (nativeTranslationGroupPolynomial w d b p) =
      bchRealTranslationHom w d hwd ⟨VectorPolynomial.eval₂ u p⟩ := by
  rw [nativeTranslationGroupPolynomial, translationLogGroupPolynomial_specialize,
    ← nativeTranslationLogCoordinate_eval]

theorem nativeTranslationGroupPolynomial_orbit (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (v : U → ℕ) (g : (weightedFiltration w d hwd).realification.PolynomialOrbit v)
    (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u) (nativeTranslationGroupPolynomial w d b g.log) =
      bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval v u g) :=
  nativeTranslationGroupPolynomial_specialize w d hwd b g.log u

theorem nativeTranslationGroupPolynomial_native (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (v : U → ℕ)
    (g : ((weightedFiltration w d hwd).realification.adaptedPolynomialFiltration v).Group)
    (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u)
        (nativeTranslationGroupPolynomial w d b g.coord.val) =
      bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).adaptedPolynomialRealValueHom v u g) :=
  nativeTranslationGroupPolynomial_specialize w d hwd b g.coord.val u

omit [Fintype κ] in

theorem nativeTranslationLogCoordinate_degree (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (ω : κ → ℕ)
    (hb : ∀ j, (weightedFiltration w d hwd).layer j =
      Submodule.span ℚ (b '' {k | j ≤ ω k}))
    (v : U → ℕ)
    (g : ((weightedFiltration w d hwd).realification.adaptedPolynomialFiltration v).Group)
    (k : κ) :
    nativeTranslationLogCoordinate w d b g.coord.val k ∈ weightedSupportLE v (ω k) :=
  (weightedFiltration w d hwd).real_adapted_coordinate_degree b ω hb
    ((weightedFiltration w d hwd).realification.adaptedBCHToOrbit v g) k

omit [Fintype κ] in

theorem nativeTranslationLogCoordinate_constant (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d))
    (hp : VectorPolynomial.coefficients p 0 = 0) (k : κ) :
    (nativeTranslationLogCoordinate w d b p k).coeff 0 = 0 := by
  rw [nativeTranslationLogCoordinate_coeff, hp, map_zero, Finsupp.zero_apply]

theorem nativeTranslationGroupPolynomial_realified (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (v : U → ℕ) (g : (weightedFiltration w d hwd).RealAdaptedPolynomialGroup v)
    (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u)
        (nativeTranslationGroupPolynomial w d b
          ((weightedFiltration w d hwd).realAdaptedPolynomialMap v g.coord)) =
      bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).adaptedPolynomialRealValueHom v u
          ((weightedFiltration w d hwd).realAdaptedPolynomialGroupHom v g)) :=
  nativeTranslationGroupPolynomial_native w d hwd b v
    ((weightedFiltration w d hwd).realAdaptedPolynomialGroupHom v g) u

omit [Fintype κ] in
@[simp] theorem nativeTranslationLogCoordinate_symbol (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (ω : κ → ℕ)
    (hb : ∀ j, (weightedFiltration w d hwd).layer j =
      Submodule.span ℚ (b '' {k | j ≤ ω k}))
    (v : U → ℕ) (g : (weightedFiltration w d hwd).RealPolynomialSymbolGroup v)
    (k : κ) :
    nativeTranslationLogCoordinate w d b
        ((weightedFiltration w d hwd).realPolynomialSymbolLift b ω hb v g).coord.val k =
      (weightedFiltration w d hwd).realSymbolCoordinate b ω hb v g.coord k := rfl

theorem nativeTranslationGroupPolynomial_symbol (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (ω : κ → ℕ)
    (hb : ∀ j, (weightedFiltration w d hwd).layer j =
      Submodule.span ℚ (b '' {k | j ≤ ω k}))
    (v : U → ℕ) (g : (weightedFiltration w d hwd).RealPolynomialSymbolGroup v)
    (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (eval u)
        (nativeTranslationGroupPolynomial w d b
          ((weightedFiltration w d hwd).realSymbolRepresentative b ω hb v g.coord)) =
      bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).adaptedPolynomialRealValueHom v u
          ((weightedFiltration w d hwd).realPolynomialSymbolLift b ω hb v g)) :=
  nativeTranslationGroupPolynomial_native w d hwd b v
    ((weightedFiltration w d hwd).realPolynomialSymbolLift b ω hb v g) u

omit [Fintype B] in
private theorem translationPolynomial_ext_eval
    (g h : PolynomialTranslationGroupOver (MvPolynomial U ℝ) B)
    (hgh : ∀ u : U → ℝ,
      PolynomialTranslationGroupOver.map (eval u) g =
        PolynomialTranslationGroupOver.map (eval u) h) : g = h := by
  apply PolynomialTranslationGroupOver.ext
  · funext i
    apply MvPolynomial.funext
    intro u
    exact congrArg (fun a => a.base i) (hgh u)
  · apply MvPolynomial.ext
    intro α
    apply MvPolynomial.funext
    intro u
    have he := congrArg (fun element => element.polynomial.coeff α) (hgh u)
    simpa only [PolynomialTranslationGroupOver.map_polynomial, coeff_map] using he

theorem nativeTranslationGroupPolynomial_mul (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (v : U → ℕ)
    (g h : ((weightedFiltration w d hwd).realification.adaptedPolynomialFiltration v).Group) :
    nativeTranslationGroupPolynomial w d b (g * h).coord.val =
      nativeTranslationGroupPolynomial w d b g.coord.val *
        nativeTranslationGroupPolynomial w d b h.coord.val := by
  apply translationPolynomial_ext_eval
  intro u
  rw [map_mul, nativeTranslationGroupPolynomial_native,
    nativeTranslationGroupPolynomial_native, nativeTranslationGroupPolynomial_native,
    map_mul, map_mul]

theorem nativeTranslationGroupPolynomial_factorization (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (v : U → ℕ)
    (e p r g : ((weightedFiltration w d hwd).realification.adaptedPolynomialFiltration v).Group)
    (hprod : e * p * r = g) :
    nativeTranslationGroupPolynomial w d b e.coord.val *
        nativeTranslationGroupPolynomial w d b p.coord.val *
          nativeTranslationGroupPolynomial w d b r.coord.val =
      nativeTranslationGroupPolynomial w d b g.coord.val := by
  rw [← nativeTranslationGroupPolynomial_mul w d hwd b v,
    ← nativeTranslationGroupPolynomial_mul w d hwd b v, hprod]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem realifyFunctional_basis_coord {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (i : ι) :
    realifyFunctional (b.coord i) = (b.baseChange ℝ).coord i := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [realifyFunctional_tmul]
    change a * (b.repr x i : ℝ) = (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] x) i
    rw [Basis.baseChange_repr_tmul]
    simp only [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace NilpotentLieFiltration

theorem scalarSymbolPolynomial_eq_sum_realSymbolCoordinates
    {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (g : F.RealPolynomialSymbolGroup w) :
    F.scalarSymbolPolynomial b ω hF w θ g =
      ∑ i, MvPolynomial.C (θ (F.associatedGradedBasis b ω hF i) : ℝ) *
        F.realSymbolCoordinate b ω hF w g.coord i := by
  classical
  ext α
  rw [F.coeff_scalarSymbolPolynomial,
    realifyFunctional_eq_sum_basis (F.associatedGradedBasis b ω hF)]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, F.coeff_realSymbolCoordinate]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : Finsupp.weight w α = ω i
  · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w g.coord ⟨(α, i), h⟩,
      F.realSymbolRepresentative_coefficient b ω hF w g.coord ⟨(α, i), h⟩,
      mul_comm]
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord α i h,
      F.realSymbolRepresentative_coefficient_of_ne b ω hF w g.coord α i h,
      zero_mul, mul_zero]

theorem scalarSymbolPolynomial_joint_grid
    {σ ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (θ : κ → F.AssociatedGraded →ₗ[ℚ] ℚ) (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g) :
    (fun z : (σ →₀ ℕ) × κ =>
      (F.scalarSymbolPolynomial b ω hF w (θ z.2) g).coeff z.1) ∈
        realDenominatorGrid (matrixDenominator (fun k i => θ k (F.associatedGradedBasis b ω hF i)) * m) := by
  classical
  let ℓ : F.AssociatedGraded →ₗ[ℚ] (κ → ℚ) := LinearMap.pi θ
  have hval (α : σ →₀ ℕ) :
      realifyCoordinateMap ℓ
        (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) =
        fun k => (F.scalarSymbolPolynomial b ω hF w (θ k) g).coeff α := by
    funext k
    rw [F.coeff_scalarSymbolPolynomial]
    rfl
  have hgrid (α : σ →₀ ℕ) :
      (fun k => (F.scalarSymbolPolynomial b ω hF w (θ k) g).coeff α) ∈
        realDenominatorGrid (matrixDenominator (fun k i => θ k (F.associatedGradedBasis b ω hF i)) * m) := by
    have h := realifyCoordinateMap_grid (F.associatedGradedBasis b ω hF) ℓ m _
      (F.realGradedSymbolPolynomial_rational_coordinates b ω hF w m g hg α)
    rw [hval] at h
    exact h
  choose a ha using hgrid
  refine ⟨fun z => a z.1 z.2, ?_⟩
  funext z
  exact congrFun (ha z.1) z.2

end NilpotentLieFiltration

namespace PolynomialTranslationLie

open RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationLogCoordinatePolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) : MvPolynomial U ℝ :=
  coordinate (((weightedBasis w d hw).baseChange ℝ).coord k).toAddMonoidHom
    (detectedTranslationSymbolLift w d hw hwd M hM D E).log

theorem detectedTranslationLogCoordinate_eq_canonical
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k =
      (weightedFiltration w d hwd).realSymbolCoordinate (weightedBasis w d hw)
        (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
        (fun _ : U => 1) (detectedTranslationSymbolProjection w d hw hwd M hM D E).coord k := by
  simp only [detectedTranslationLogCoordinatePolynomial, detectedTranslationSymbolLift_log,
    NilpotentLieFiltration.realSymbolCoordinate, detectedTranslationSymbolProjection_coord]

theorem detectedTranslationLogCoordinate_homogeneous
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).IsWeightedHomogeneous
      (fun _ : U => 1) (weightedBasisGrade w d k) := by
  rw [detectedTranslationLogCoordinate_eq_canonical]
  exact (weightedFiltration w d hwd).realSymbolCoordinate_isWeightedHomogeneous
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) _ _ k

@[simp] theorem detectedTranslationLogCoordinate_constant
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).coeff 0 = 0 := by
  rw [detectedTranslationLogCoordinate_eq_canonical]
  exact (weightedFiltration w d hwd).realSymbolCoordinate_coeff_zero
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) _ _ k

noncomputable def detectedTranslationLogFunctional (k : WeightedBasisIndex w d) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded →ₗ[ℚ] ℚ :=
  ((weightedBasis w d hw).coord k).comp
    (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
      w d hw hwd (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).toLinearMap

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationLogCoordinate_eq_scalar
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k =
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
        b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D k) E := by
  rw [detectedTranslationLogCoordinatePolynomial, detectedTranslationSymbolLift_log]
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.homogeneousProjected_scalar_coordinate
    (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    (fun _ : U => 1) ((weightedBasis w d hw).coord k) E.coord
  rw [realifyFunctional_basis_coord] at h
  change (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
    b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D k) E = _ at h
  convert h.symm using 1

noncomputable def detectedTranslationLogProjectionMatrix : Matrix (WeightedBasisIndex w d) ι ℚ :=
  fun k i => if ω i = weightedBasisGrade w d k then (weightedBasis w d hw).repr (b i true) k else 0

theorem detectedTranslationLogFunctional_basis (k : WeightedBasisIndex w d) (i : ι) :
    detectedTranslationLogFunctional w d hw hwd M hM D k
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN i) =
      detectedTranslationLogProjectionMatrix w d hw b ω k i := by
  exact (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.homogeneousGradedProjection_basis_repr
    (weightedFiltration w d hwd) (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    b ω hN i k

theorem detectedTranslationLogCoordinate_eq_sum [Fintype ι]
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k =
      ∑ i, MvPolynomial.C (detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ) *
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.realSymbolCoordinate
          b ω hN (fun _ : U => 1) E.coord i := by
  rw [detectedTranslationLogCoordinate_eq_scalar w d hw hwd M hM D b ω hN]
  rw [NilpotentLieFiltration.scalarSymbolPolynomial_eq_sum_realSymbolCoordinates]
  simp only [detectedTranslationLogFunctional_basis w d hw hwd M hM D b ω hN]

theorem detectedTranslationLogCoordinate_slow_coefficients [Fintype ι]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (k : WeightedBasisIndex w d)
    (hproj : ∀ i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) (α : U →₀ ℕ) :
    |(detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).coeff α| ≤
      (Fintype.card ι : ℝ) * H * A / monomialScale T α := by
  rw [detectedTranslationLogCoordinate_eq_scalar w d hw hwd M hM D b ω hN]
  apply NilpotentLieFiltration.scalarSymbolPolynomial_slow_coefficients
    _ b ω hN _ _ T hT hA hH _ E hE α
  intro i
  simpa only [detectedTranslationLogFunctional_basis w d hw hwd M hM D b ω hN] using hproj i

theorem detectedTranslationLogCoordinate_joint_grid [Fintype ι]
    (m : ℕ)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m E) :
    (fun z : (U →₀ ℕ) × WeightedBasisIndex w d =>
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E z.2).coeff z.1)
        ∈ realDenominatorGrid (matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m) := by
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_joint_grid
    b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D) m E hE
  simpa only [detectedTranslationLogFunctional_basis w d hw hwd M hM D b ω hN,
    ← detectedTranslationLogCoordinate_eq_scalar w d hw hwd M hM D b ω hN] using h

theorem detectedTranslationLogCoordinate_rational_coefficients [Fintype ι]
    (m : ℕ)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m E) (k : WeightedBasisIndex w d) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun (_ : Unit) i => detectedTranslationLogProjectionMatrix w d hw b ω k i) * m)
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) := by
  rw [detectedTranslationLogCoordinate_eq_scalar w d hw hwd M hM D b ω hN]
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_rational_coefficients
    b ω hN (fun _ : U => 1) (detectedTranslationLogFunctional w d hw hwd M hM D k) m E hE
  simpa only [detectedTranslationLogFunctional_basis w d hw hwd M hM D b ω hN] using h

theorem detectedTranslationLogCoordinate_exists_coefficient_grid [Fintype ι]
    (k : WeightedBasisIndex w d) {H : ℕ}
    (hproj : ∀ i, RationalHeightLE (detectedTranslationLogProjectionMatrix w d hw b ω k i) H)
    (m : ℕ) (hm : 0 < m)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m E) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ Fintype.card ι * m ∧
      realPolynomialCoefficientGrid q (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) := by
  rw [detectedTranslationLogCoordinate_eq_scalar w d hw hwd M hM D b ω hN]
  apply NilpotentLieFiltration.scalarSymbolPolynomial_exists_coefficient_grid
    _ b ω hN _ _ _ m hm E hE
  intro i
  simpa only [detectedTranslationLogFunctional_basis w d hw hwd M hM D b ω hN] using hproj i

theorem detectedTranslationLogCoordinate_common_coefficient_grid [Fintype ι]
    (m : ℕ)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m E) (k : WeightedBasisIndex w d) :
    realPolynomialCoefficientGrid
      (matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m)
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) := by
  obtain ⟨a, ha⟩ := detectedTranslationLogCoordinate_joint_grid w d hw hwd M hM D b ω hN m E hE
  refine ⟨fun α => a (α, k), ?_⟩
  funext α
  exact congrFun ha (α, k)

theorem exists_detectedTranslationLogCoordinate_common_grid [Fintype ι]
    {H : ℕ}
    (hproj : ∀ k i, RationalHeightLE (detectedTranslationLogProjectionMatrix w d hw b ω k i) H)
    (m : ℕ) (hm : 0 < m) :
    ∃ q : ℕ, 0 < q ∧
      q ≤ H ^ (Fintype.card (WeightedBasisIndex w d) * Fintype.card ι) * m ∧
      ∀ E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1),
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
          b ω hN (fun _ : U => 1) m E →
        ∀ k, realPolynomialCoefficientGrid q
          (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k) := by
  refine ⟨matrixDenominator (detectedTranslationLogProjectionMatrix w d hw b ω) * m,
    Nat.mul_pos (matrixDenominator_pos _) hm,
    Nat.mul_le_mul_right m (matrixDenominator_le _ hproj), ?_⟩
  intro E hE k
  exact detectedTranslationLogCoordinate_common_coefficient_grid w d hw hwd M hM D b ω hN m E hE k

omit [Fintype (WeightedBasisIndex w d)] in
theorem detectedTranslationLogProjectionMatrix_height {H : ℕ} (hH : 1 ≤ H)
    (hproj : ∀ k i, RationalHeightLE ((weightedBasis w d hw).repr (b i true) k) H)
    (k : WeightedBasisIndex w d) (i : ι) :
    RationalHeightLE (detectedTranslationLogProjectionMatrix w d hw b ω k i) H := by
  classical
  unfold detectedTranslationLogProjectionMatrix
  split_ifs
  · exact hproj k i
  · exact rationalHeightLE_zero hH

end PolynomialTranslationLie
end Erdos3

end

end OAI
