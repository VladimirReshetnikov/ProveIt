import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath

namespace OAI

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A] {Dmod : ℕ} {selected : A → Σ j, Fin (n j)}
variable {τ δslice : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

omit [Fintype A] in
theorem transitionLip_le_Pcap : (s.L : ℝ) ≤ s.Pcap := by
  have h := s.hprimitiveCap
  have hpad : 0 ≤ paddedResidueDensityCap Empty 1 := by
    unfold paddedResidueDensityCap scalarCubeResidueDensityCap
    positivity
  norm_num [scalarCubePrimitiveEnvelope, scalarCubeCutoffDerivativeNumerator,
    scalarCubeGridBoundaryConstant] at h
  linarith [s.L.coe_nonneg]

omit [Fintype A] in
theorem transitionLip_le_exp : (s.L : ℝ) ≤ Real.exp s.pcap :=
  s.transitionLip_le_Pcap.trans s.hPcapp

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup

end

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} {Dmod : ℕ} {selected : A → Σ j, Fin (n j)}
variable {τ δslice : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

noncomputable def slicedComparisonSourceLog (Ptest : ℝ) : ℝ :=
  2 + s.D * s.D + s.pcap + max 0 Ptest

theorem slicedComparisonSourceLog_bounds (Ptest : ℝ) :
    2 ≤ s.slicedComparisonSourceLog Ptest ∧
    s.D * s.D ≤ s.slicedComparisonSourceLog Ptest ∧
    (s.L : ℝ) ≤ Real.exp (s.slicedComparisonSourceLog Ptest) ∧
    Ptest ≤ s.slicedComparisonSourceLog Ptest := by
  have hD := mul_self_nonneg s.D
  have hc := s.hpcap
  have hmax : 0 ≤ max 0 Ptest := le_max_left _ _
  have htest : Ptest ≤ max 0 Ptest := le_max_right _ _
  have hpc : s.pcap ≤ s.slicedComparisonSourceLog Ptest := by
    unfold slicedComparisonSourceLog
    linarith
  refine ⟨?_, ?_, s.transitionLip_le_exp.trans (Real.exp_le_exp.mpr hpc), ?_⟩ <;>
    unfold slicedComparisonSourceLog <;> linarith

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup

end

end OAI
