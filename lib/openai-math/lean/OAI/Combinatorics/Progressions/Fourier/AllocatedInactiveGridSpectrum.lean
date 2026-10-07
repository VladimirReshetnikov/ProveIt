import OAI.Combinatorics.Progressions.Lattices.AllocatedInactiveResidueScale
import OAI.Combinatorics.Progressions.Lattices.WeightedModerateIntegerApproximation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "source" => allocatedLocalResidueSources B U b S j i q hq r hsize
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

theorem exists_allocated_inactive_grid_spectrum
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P ε : ℝ)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    letI : NeZero height := ⟨(basisAxisScale_pos (b j) i).ne'⟩
    let ζ := uniformBlockRetainedBias j.val rows.card (degree * rows.card) P
      ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ε
    ∃ F : Finset (rows → Fin (torus * height)),
      (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card (degree * rows.card) P
        ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) /
          ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * (degree * rows.card)) ∧
      (∑ k, ‖∏ a, weightedCubeGridCoefficient (source a) (torus * height) rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card (degree * rows.card) P
          ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ∧
      (∀ k ∈ F, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤
        uniformCharacterDenominatorBound j.val rows.card (degree * rows.card) P
          ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ rows.card) ζ ∧
        ∃ (a : rows → ℤ) (ξ : rows → ℝ),
          (∀ t, |ξ t| ≤ 2 * majorArcCoverConstant j.val rows.card P ((torus : ℝ) * cost) /
            ζ ^ majorArcCoverExponent j.val rows.card) ∧
          ∀ t, ((k t).val : ℝ) / (torus * height) = (a t : ℝ) / d + ξ t / height) ∧
      ∀ shift z : rows → ℤ,
        (∀ t, |(z t : ℝ) - shift t| ≤ blockJetScaleBound (Fintype.card α) degree
          (Fintype.card (B ⟨j, Sum.inr i⟩)) 1 * height) →
        ‖(((height : ℝ) ^ rows.card *
            (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows shift z).toReal : ℝ) : ℂ) -
          weightedCubeGridApproximation source height (torus * height) rows shift z F‖ ≤ ε := by
  let : NeZero height := ⟨(basisAxisScale_pos (b j) i).ne'⟩
  have hs (a : B ⟨j, Sum.inr i⟩) (v : Fin degree) : ScalarCubePrimitiveBudget (source a v) A P :=
    (allocatedLocalResidueSources_primitive B U b S j i q hq r hsize a v A).mono hP
  have hP1 : 1 ≤ P :=
    (hs (Classical.choice (inferInstance : Nonempty (B ⟨j, Sum.inr i⟩))) ⟨0, Nat.zero_lt_succ _⟩).one_le
  obtain ⟨hu, hl, hp⟩ := allocatedInactiveResidueSources_scale B U b S j i q hq r hsize hsmall hlarge
  obtain ⟨F, hcard, hcap, hchar, herr⟩ := weightedCube_integer_density_approximation (K := height)
    source A hA hP1 zero_le_one (by positivity) (by positivity) hε hε1 hs
    (fun a => by simpa only [one_mul] using hu a) hl degree hp rows hrows hB
  refine ⟨F, hcard, hcap, hchar, ?_⟩
  intro shift z hz
  have h := herr shift z hz
  rw [finiteImageMass_eq_toPMF,
    allocatedInactiveResidueJetPMF_source B U b S j i q hq r hsize hR hσ hsmall hlarge hcell rows shift] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
