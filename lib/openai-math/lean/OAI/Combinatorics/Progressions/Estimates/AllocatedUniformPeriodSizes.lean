import OAI.Combinatorics.Progressions.Sampling.AllocatedCommonUniformSampling

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX uT

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S

variable {T : Type uT} (period : T → ℕ) [∀ t, NeZero (period t)] (M₀ : ℕ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} //
  allocatedActiveGrid B U b S a} → ℕ) [∀ a, NeZero (M a)]
variable {p₀ p₁ w v E : ℝ}
local notation "P" => canonicalScalarSourceEnvelope m M₀
local notation "δ" => allocatedSitePrimitiveTolerance m p₁ w v E
local notation "Λ" => allocatedSiteSpectrumLog m p₁ w v E
local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ

theorem exists_allocated_uniform_period_sampling_of_sizes
    (hp₀ : 0 ≤ p₀) (hcutoff : (M₀ : ℝ) ≤ Real.exp p₀)
    (hSourceLog : canonicalScalarSourceLog m p₀ ≤ p₁)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn : ∀ j, (n j : ℝ) ≤ p₁)
    (hperiod : ∀ t, period t ≤ M₀ ^ (m + 1))
    (hsize : ∀ t, (Fintype.card (Fin dim) + 1) * period t ≤ S.value)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (hM : ∀ a, M a = allocatedGridTorusFactor B (Fin dim) (ig a.val) *
      allocatedGridNaturalScale B U b S a.val)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩)) :
    ∃ witnesses : (t : T) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (period t) r.val,
      (∀ t r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M (witnesses t r).expansion) ∧
      ∀ t r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (period t) (witnesses t r) δ := by
  have hp₁ := (canonicalScalarSourceLog_bounds m hp₀).1.trans hSourceLog
  have hPp := (canonicalScalarSourceEnvelope_le_exp m hp₀ hcutoff).trans
    (Real.exp_le_exp.mpr hSourceLog)
  obtain ⟨hP, hcP, hsources⟩ := canonicalScalarSourceEnvelope_bounds m M₀
  have hδ := allocatedSitePrimitiveTolerance_pos m p₁ w v E
  have hΛ := (allocatedSiteSpectrumLog_bounds m hp₁ hw hv hE).2.2.2.1
  have hspec := allocatedSiteSpectrum_primitive_budget B rowSets
    (by simpa only [Fintype.card_fin] using hdimSmall) hp₁ hw hv hE hP hPp hvars hI hn
  have hsourceFamily (t : T) :
      scalarCubePrimitiveEnvelope (Fin dim) scalarSourceTransitionBound 1 0 (period t) ≤ P :=
    (scalarCubePrimitiveEnvelope_mono (Fin dim) scalarSourceTransitionBound
      (le_refl (1 : ℝ≥0)) (le_refl (0 : ℝ≥0)) (hperiod t)).trans (hsources dim hdimSmall)
  have hex (t : T) := exists_allocated_residue_site_sampling.{uG,uI,uB,uJ,uQ,uX}
    B U b hR hσ S (period t) (Nat.pos_of_ne_zero (NeZero.ne (period t))) (hsize t)
    P δ Λ M hP hδ hΛ hgamma scalarSourceTransitionBound scalarSourceTransitionBound_spec.2
    hcP (hsourceFamily t) hM hB
    (fun a => (hspec (ig a.val)).1)
    (fun a => (hspec (ig a.val)).2.1)
    (fun a => (hspec (ig a.val)).2.2)
  choose witnesses hBounds hWitnesses using hex
  exact ⟨witnesses, hBounds, hWitnesses⟩

end Erdos3.VectorPolynomial

end

end OAI
