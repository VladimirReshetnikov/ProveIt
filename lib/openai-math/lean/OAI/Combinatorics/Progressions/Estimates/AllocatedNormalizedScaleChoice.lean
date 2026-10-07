import OAI.Combinatorics.Progressions.Dynamics.AllocatedNormalizedScaleBudget
import OAI.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedNormalizedInitialScale (m : ℕ) (p Pc E T : ℝ) : ℕ :=
  ⌈Real.exp (allocatedNormalizedInitialLog m p Pc E T)⌉₊

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedNormalizedScale (p Pc E T : ℝ) :
    LayerSamplerScale (G := G) B U b R σ :=
  selectedLayerSamplerScale (G := G) B U b R σ hR hσ (allocatedNormalizedInitialScale m p Pc E T)

theorem allocatedNormalizedScale_lower (p Pc E T : ℝ) :
    Real.exp (allocatedNormalizedInitialLog m p Pc E T) ≤
      ((allocatedNormalizedScale (G := G) B U b hR hσ p Pc E T).value : ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr
    (selectedLayerSamplerScale_bounds (G := G) B U b R σ hR hσ
      (allocatedNormalizedInitialScale m p Pc E T)).1)

theorem allocatedNormalizedScale_upper {p Pc E T : ℝ}
    (hp : 0 ≤ p) (hPc : 0 ≤ Pc) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hn : ∀ j, (n j : ℝ) ≤ p)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc) :
    ((allocatedNormalizedScale (G := G) B U b hR hσ p Pc E T).value : ℝ) ≤
      Real.exp (allocatedNormalizedScaleLog m p Pc E T) := by
  obtain ⟨_, hm, hpD, _, hcount, _, _, _, hprofile⟩ := allocatedComparisonDimension_bounds m hp
  obtain ⟨hL, hQ, hDQ, hPcQ, hLQ, _⟩ := allocatedNormalizedScaleBudget_bounds m hp hPc hE hT
  let Q := allocatedNormalizedScaleInput m p Pc E T
  have hmQ : (m : ℝ) ≤ Q :=
    (Nat.cast_le.mpr (Nat.le_succ m)).trans (hm.trans hDQ)
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Q :=
    (probabilityProfileLipschitz_le_comparisonProfileBound.trans (hprofile.trans hDQ)).trans
      (by linarith [Real.add_one_le_exp Q])
  have hL₀ : (allocatedNormalizedInitialScale m p Pc E T : ℝ) ≤ Real.exp Q :=
    (natCeil_le_exp_succ_of_le hL le_rfl).trans (Real.exp_le_exp.mpr hLQ)
  exact selectedLayerSamplerScale_exp_bound (G := G) B U b R σ hR hσ _ hQ hmQ
    (fun j => (hn j).trans (hpD.trans hDQ))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hPcQ))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hPcQ))
    (fun j => (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
      (Nat.succ_le_of_lt j.isLt) hp hvars).trans (hcount.trans hDQ)) hA hL₀

theorem allocatedNormalizedScale_ready
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ m + 1)
    (hinj : ∀ j, Function.Injective (rows j)) (X : Type*) [Fintype X]
    {p Pc E T : ℝ} (hp : 0 ≤ p) (hPc : 0 ≤ Pc) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    Real.exp (allocatedRefinedJointLengthLog (G := G) B α O Pc
      (allocatedCoefficientAccuracyLog m p (E + 3))
      ((m + 1 : ℕ) * Pc + Fintype.card X * T)) ≤
        ((allocatedNormalizedScale (G := G) B U b hR hσ p Pc E T).value : ℝ) :=
  (Real.exp_le_exp.mpr (allocatedRefinedLengthLog_le_normalizedInitial B rows hq hinj X
    hp hPc hE hT hvars hI hn hX)).trans
      (allocatedNormalizedScale_lower (G := G) B U b hR hσ p Pc E T)

end Erdos3.VectorPolynomial

end

end OAI
