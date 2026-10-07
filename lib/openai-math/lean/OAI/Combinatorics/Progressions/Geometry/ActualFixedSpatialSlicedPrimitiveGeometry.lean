import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

noncomputable def slicedGeometryDimension : ℝ := s.P + (layerTailDegree m + 1 : ℕ) + 1
noncomputable def slicedGeometryRadiusLog : ℝ := s.P + s.Pscale

omit [DecidableEq X] in
theorem sliced_primitive_geometry_bounds (hR : ∀ j, 0 < R j) :
    1 ≤ s.slicedGeometryDimension ∧
    (Fintype.card A : ℝ) ≤ s.slicedGeometryDimension ∧
    (∀ a, (((selected a).1.val + 1 : ℕ) : ℝ) ≤ s.slicedGeometryDimension) ∧
    ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ s.slicedGeometryDimension ∧
    (∀ a, (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤ s.slicedGeometryDimension) ∧
    0 ≤ s.slicedGeometryRadiusLog ∧
    (∀ a, 0 < R (selected a).1) ∧
    (∀ a, R (selected a).1 ≤ Real.exp s.slicedGeometryRadiusLog) ∧
    (∀ a, (R (selected a).1)⁻¹ ≤ Real.exp s.slicedGeometryRadiusLog) ∧
    (∀ a, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1)) : ℝ) ≤ Real.exp s.slicedGeometryRadiusLog) := by
  have hP0 : 0 ≤ s.P := zero_le_one.trans s.hP
  have hPD : s.P ≤ s.slicedGeometryDimension := by
    dsimp [slicedGeometryDimension]
    have := Nat.cast_nonneg (α := ℝ) (layerTailDegree m + 1)
    linarith
  have hDg : s.D ≤ s.slicedGeometryDimension := s.hDP.trans hPD
  have hvg : 0 ≤ s.slicedGeometryRadiusLog := add_nonneg hP0 s.hPscale
  have hPvg : s.P ≤ s.slicedGeometryRadiusLog := le_add_of_nonneg_right s.hPscale
  have hScalevg : s.Pscale ≤ s.slicedGeometryRadiusLog := le_add_of_nonneg_left hP0
  have hcardA : (Fintype.card A : ℝ) ≤ s.D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected s.hselected)).trans
      (allocatedIntegerAxes_card_le B (fun _ => Finset.univ : Fin m → Finset (Finset Empty)) s.hD)
  refine ⟨s.hP.trans hPD, hcardA.trans hDg, ?_, ?_, ?_, hvg,
    fun a => hR (selected a).1, ?_, ?_, ?_⟩
  · intro a
    exact (s.hD.layer_degree B (selected a).1).trans hDg
  · dsimp [slicedGeometryDimension]
    linarith
  · intro a
    have hblock : (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤
        ∑ v : LayerSamplerAxis I n, (Fintype.card (B v) : ℝ) :=
      Finset.single_le_sum
        (f := fun v : LayerSamplerAxis I n => (Fintype.card (B v) : ℝ))
        (fun _ _ => Nat.cast_nonneg _)
        (Finset.mem_univ (⟨(selected a).1, Sum.inr (selected a).2⟩ : LayerSamplerAxis I n))
    exact (hblock.trans s.hblocks).trans hPD
  · intro a
    exact (s.hR1 a).trans (Real.one_le_exp_iff.mpr hvg)
  · intro a
    exact (s.hRinv a).trans (Real.exp_le_exp.mpr hScalevg)
  · intro a
    exact ((s.hD.coefficients (selected a).1).trans s.hDP).trans
      ((by linarith [Real.add_one_le_exp s.P] : s.P ≤ Real.exp s.P).trans
        (Real.exp_le_exp.mpr hPvg))

omit [DecidableEq X] [Fintype A] in
theorem sliced_ambient_coordinate_cutoff_bounds :
    let Lcoord := s.K * ∑ j, s.forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * s.radius)) * Lcoord
    (Lcoord : ℝ) ≤ Real.exp (s.PK + s.PF + s.D) ∧
    (Lcut : ℝ) ≤ Real.exp (s.PK + s.PF + 2 * s.D + normalizedSiteCutoffBound + 1) := by
  apply forecast_ambient_coordinate_cutoff_exp_bounds s.forward s.K s.radius
    s.hD.nonneg s.hPK s.hPF s.hdim s.haxes s.hforwardBound s.hKBound
  have h3 := s.hr3
  change (1 : ℝ) ≤ (s.radius : ℝ)
  linarith

omit [DecidableEq X] [Fintype A] in
theorem sliced_spatial_coordinate_bound :
    (max ⟨8 / τ, by have := s.hτ; positivity⟩ 1 : ℝ≥0) ≤
      ⟨Real.exp (s.Pτ + 8), Real.exp_nonneg _⟩ :=
  forecast_spatial_coordinate_exp_bound s.hτ s.hPτ s.hτinv

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

end OAI
