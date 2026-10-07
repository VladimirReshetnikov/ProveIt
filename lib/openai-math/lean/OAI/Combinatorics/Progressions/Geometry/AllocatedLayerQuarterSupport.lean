import OAI.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
import OAI.Combinatorics.Progressions.Estimates.MixedRealPoint

namespace OAI

section

namespace Erdos3

open Module Submodule

theorem mixedCoefficient_quarter_support {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart W b).symm x‖ ≤ C * ‖x‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1/4)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (hcw : ∀ i, |c i| + w i ≤ R)
    (p : Fin n → PMF ℤ)
    (hp : ∀ i k, k ∈ (p i).support → |(k : ℝ) / basisAxisScale b i| ≤ R)
    (x : (I → ℝ) × (Fin n → ℤ)) (hx : mixedCoefficientDensity c w p x ≠ 0) :
    ∀ d, |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4 := by
  obtain ⟨hu, hz⟩ := (mixedCoefficientDensity_support c w p x).mp hx
  have hn := mixedRealPoint_norm_le W b o hC hR hchart x.1
    (fun i => (x.2 i : ℝ) / basisAxisScale b i)
    (fun i => (affineProbabilityProfile_abs_le _ (hw i) (hu i)).trans (hcw i))
    (fun i => hp i _ (hz i))
  rw [mixedRealPoint_integer] at hn
  have hquarter : ‖normalizedLatticePoint W b (orthonormalMixedChart o x)‖ ≤ 1/4 :=
    hn.trans (by simpa only [mul_assoc] using hsmall)
  intro d
  have hd : |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤
      ‖normalizedLatticePoint W b (orthonormalMixedChart o x)‖ := by
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (normalizedLatticePoint W b (orthonormalMixedChart o x)) d
  exact hd.trans hquarter

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
variable (Pc : I → Finset J)

local notation "intLaws" => allocatedProjectionPMFs W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL

theorem allocatedArrayColumns_quarter_support (o : OrthonormalBasis I ℝ W)
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (j : J) (x : (I → ℝ) × (Fin n → ℤ))
    (hx : mixedCoefficientDensity (fun i => allocatedArrayCenters e T Pc R i j)
      (fun i => allocatedArrayWidths e T Pc j₀ R σ i j) (fun i => intLaws i j) x ≠ 0) :
    ∀ d, |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4 := by
  apply mixedCoefficient_quarter_support W b o hC hR.le hchart hsmall _ _
    (fun i => allocatedArrayWidths_pos e T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) Pc j₀ hR hσ i j)
    (fun i => allocatedArrayProfiles_bound e T hT Pc j₀ hc₀ hR hσ hσ1 i j) _ _ x hx
  intro i k hk
  apply scaledAbs_le_of_bound (one_le_monomialScale T hT (e j))
  exact (allocatedIntegerCoefficient_bound (Pz i) j₀ h (basisAxisScale b i) L s hh
    (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
    R σ hR hσ hσ1 (hgap i) hεL (hz₀ i) he₀ (hprincipal i) j hk).trans (by linarith)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem allocatedLayerColumns_quarter_support (hσ1 : ∀ j, σ j ≤ 1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (j : Fin m) (d) (x)
    (hx : mixedCoefficientDensity (fun i => allocatedLayerCenters B U b S j i d)
      (fun i => allocatedLayerWidths B U b S j i d)
      (fun i => allocatedLayerIntegerPMFs B U b hR hσ S j i d) x ≠ 0) :
    ∀ a, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4 := by
  exact allocatedArrayColumns_quarter_support (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)
    (layerContinuousPrincipalSlots B j) (o j) (layerContinuousPrincipalSlots_not_constant B j)
    (layerIntegerPrincipalSlots_not_constant B j) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U b R S.value j) (hC j) (hchart j) (hsmall j) d x hx

end Erdos3.VectorPolynomial

end

end OAI
