import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
import OAI.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {I ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem realSymbolFactorization_freeze
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℝ)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : I => 1)).Group)
    (E P R : F.RealPolynomialSymbolGroup (fun _ : I => 1))
    (hfactor : E * P * R = F.realPolynomialSymbolHom b ω hF (fun _ : I => 1) g)
    (hP : P.coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : I => 1) U))
    (T : I → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hE : F.SymbolSlowBound b ω hF (fun _ : I => 1) T M E)
    (q : ℕ) (hR : F.SymbolRationalGrid b ω hF (fun _ : I => 1) q R) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fun _ : I => 1)
      (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
      (frozenCoordinate_zero_homogeneous keep)
    pull E * pull P * pull R = F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : I => 1) (fun _ : {i // keep i} => 1)
        (frozenCoordinate keep fixed) (frozenCoordinate_support keep fixed) g) ∧
    (pull P).coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i // keep i} => 1) U) ∧
    F.SymbolSlowBound b ω hF (fun _ : {i // keep i} => 1) (fun i => T i.val) M (pull E) ∧
    F.SymbolRationalGrid b ω hF (fun _ : {i // keep i} => 1) q (pull R) := by
  intro pull
  have hsymbolZero := F.realPolynomialSymbolHom_homogeneousChart b ω hF
    (fun _ : I => 1) (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
    (frozenCoordinate_zero_homogeneous keep) g
    (F.weightedAdaptedRealChartHom (fun _ : I => 1) (fun _ : {i // keep i} => 1)
      (frozenCoordinate keep 0) (frozenCoordinate_support keep 0) g)
    (F.weightedAdaptedRealChartHom_coord _ _ _ _ g)
  have hfiber : F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : I => 1) (fun _ : {i // keep i} => 1)
        (frozenCoordinate keep 0) (frozenCoordinate_support keep 0) g) =
      F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : I => 1) (fun _ : {i // keep i} => 1)
        (frozenCoordinate keep fixed) (frozenCoordinate_support keep fixed) g) := by
    simpa only [freezePolynomial, aeval_X] using
      F.realPolynomialSymbolHom_frozenChart_independent b ω hF (fun _ : I => 1)
        (fun i => X i) (fun i => weightedSupportLE_X (R := ℝ) (fun _ : I => 1) i)
        keep 0 fixed g
  refine ⟨?_, F.realSymbolHomogeneousPullback_mem_pointwise b ω hF _ _ _ _ U P hP,
    F.symbolSlowBound_freeze_zero b ω hF keep T hT hM E hE, ?_⟩
  · calc
      _ = pull (E * P * R) := by rw [map_mul, map_mul]
      _ = pull (F.realPolynomialSymbolHom b ω hF (fun _ : I => 1) g) := congrArg pull hfactor
      _ = _ := hsymbolZero.symm.trans hfiber
  · apply F.symbolRationalGrid_homogeneousPullback_integral b ω hF
      (fun _ : I => 1) (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
      (frozenCoordinate_zero_homogeneous keep) ?_ q R hR
    intro i
    have hcast : MvPolynomial.map (Int.castRingHom ℝ)
        (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i) =
        frozenCoordinate keep (0 : {i // ¬keep i} → ℝ) i := by
      by_cases hi : keep i <;> simp [frozenCoordinate, hi]
    exact hcast ▸ realPolynomialCoefficientGrid_intCast
      (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom symbolPointwiseSubalgebra realificationLieSubalgebra

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable {m : ℕ} {G X : Type*} [Fintype G] {I J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U btag R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem HasCommonRefilteredOrbitFactors.allocatedFrozenSymbolFactors
    (c : ∀ j, U j) (origin : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (q : ℝ) (l : ℕ) (fast : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF (layerSamplerBox B U btag S) q l fast
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : LayerSamplerVariables G I n B => 1)
        (integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U btag otag poly hm c origin v sample))
        (allocatedRecoveredIntegerFullChart_support B U btag otag poly hm c origin v sample) g)) :
    ∃ El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : {i // keep i} => 1),
      El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : {i // keep i} => 1)
          (integerSampledRealChart
            (allocatedFrozenIntegerFullChart B U btag otag poly hm c origin v sample keep fixed))
          (allocatedFrozenIntegerFullChart_support B U btag otag poly hm c origin v sample keep fixed) g) ∧
      Pl.coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i // keep i} => 1) fast) ∧
      F.SymbolSlowBound b ω hF (fun _ : {i // keep i} => 1)
        (fun i => ((Sum.elim (fun _ : G => S.value)
          (allocatedPrincipalSides B U btag S) i.val : ℕ) : ℝ)) (Real.exp q) El ∧
      F.SymbolRationalGrid b ω hF (fun _ : {i // keep i} => 1) l Rl := by
  let gLocal := F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
    (fun _ : LayerSamplerVariables G I n B => 1)
    (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U btag otag poly hm c origin v sample))
    (allocatedRecoveredIntegerFullChart_support B U btag otag poly hm c origin v sample) g
  obtain ⟨E, P, Rl, hfactor, hP, hE, hRl⟩ :=
    h.symbolFactors F b ω hF (layerSamplerBox B U btag S) q l fast gLocal
  have hfrozen := F.realSymbolFactorization_freeze b ω hF keep (fun i => (fixed i : ℝ)) fast
    gLocal E P Rl hfactor hP (layerSamplerBox B U btag S)
    (fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U btag S i))
    (Real.exp_nonneg q) hE l hRl
  dsimp only at hfrozen
  obtain ⟨hproduct, hmiddle, hslow, hgrid⟩ := hfrozen
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF
    (fun _ : LayerSamplerVariables G I n B => 1) (fun _ : {i // keep i} => 1)
    (frozenCoordinate keep 0) (frozenCoordinate_zero_homogeneous keep)
  refine ⟨pull E, pull P, pull Rl, ?_, hmiddle, ?_, hgrid⟩
  · rw [F.weightedAdaptedRealChartHom_allocatedFrozenIntegerFullChart B U btag otag poly hm
      c origin v sample keep fixed g]
    exact hproduct
  · simpa only [allocatedParameterBox_side_eq] using hslow

end Erdos3.NilpotentLieFiltration

end

end OAI
