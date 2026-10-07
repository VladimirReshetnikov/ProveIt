import OAI.Combinatorics.Progressions.Estimates.AllocatedSiteBufferLog
import OAI.Combinatorics.Progressions.Estimates.MixedCoveredSiteExtraction

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedSiteJetSize (α : Type*) [Fintype α] (j : Fin m) : ℝ :=
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
    ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) + idealSiteEnvelopeRadius α m

theorem allocatedSiteJetSize_nonneg (α : Type*) [Fintype α] (j : Fin m) :
    0 ≤ allocatedSiteJetSize (G := G) B α j := by
  have h := (idealSiteEnvelopeRadius_pos α m).le
  unfold allocatedSiteJetSize
  positivity

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "rows" => (fun j : Fin m => (Subtype.val : jets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit jets I n grid

theorem allocatedSiteBox_mixed_coordinate_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (z : ∀ j, (I j → jets j → ℝ) × (Fin (n j) → jets j → ℤ))
    (hz : allocatedGridJetDensity B U b hR hσ S x u v rows
      (fun a => coefficientJetAxisEquiv jets I n z a.val) ≠ 0)
    (hsites : ∀ s a, |allocatedIdealSiteCoordinates B U b S (split z).2 s a| ≤ 2 * idealSiteBoxRadius α m)
    (j : Fin m) (r : jets j) :
    (∀ i, |(z j).1 i r| ≤ allocatedSiteJetSize (G := G) B α j * R j) ∧
      (∀ i, |((z j).2 i r : ℝ) / basisAxisScale (b j) i| ≤ allocatedSiteJetSize (G := G) B α j * R j) := by
  have hnorm := allocatedIdealNormalizedJets_bound_of_sites B U b S (split z).2
    (mul_nonneg (by norm_num) (idealSiteBoxRadius_pos α m).le) hsites
  have hactive (a : {a // ¬grid a}) (t : jets a.val.1) :
      |allocatedLongJetRealCoordinates B U b S (split z).2 ⟨a, t⟩| ≤
        idealSiteEnvelopeRadius α m * R a.val.1 := by
    have h := (norm_le_pi_norm (fun q : (Σ a : {a // ¬grid a}, jets a.val.1) =>
      allocatedLongJetRealCoordinates B U b S (split z).2 q / R q.1.val.1) ⟨a, t⟩).trans hnorm
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hR a.val.1)] at h
    exact (div_le_iff₀ (hR a.val.1)).mp h
  have hlong : idealSiteEnvelopeRadius α m ≤ allocatedSiteJetSize (G := G) B α j := by
    unfold allocatedSiteJetSize
    exact le_add_of_nonneg_left (by positivity)
  constructor
  · intro i
    exact (hactive ⟨⟨j, Sum.inl i⟩, by change ¬False; exact not_false⟩ r).trans
      (mul_le_mul_of_nonneg_right hlong (hR j).le)
  · intro i
    by_cases hg : grid ⟨j, Sum.inr i⟩
    · have h := allocatedGridJetDensity_scaled_support_bound B U b hR hσ S x u v rows z hz j (hσ1 j) i hg r
      apply h.trans
      apply mul_le_mul_of_nonneg_right _ (hR j).le
      exact le_add_of_nonneg_right (idealSiteEnvelopeRadius_pos α m).le
    · exact (hactive ⟨⟨j, Sum.inr i⟩, hg⟩ r).trans
        (mul_le_mul_of_nonneg_right hlong (hR j).le)

theorem allocatedSiteBox_mixed_point_bound (hσ1 : ∀ j, σ j ≤ 1)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} (d : ℕ) (z : MixedCoveredJetSource I jets Q n d)
    (hz : allocatedGridJetDensity B U b hR hσ S x u v rows
      (fun a => coefficientJetAxisEquiv jets I n z.1 a.val) ≠ 0)
    (hsites : ∀ s a, |allocatedIdealSiteCoordinates B U b S (split z.1).2 s a| ≤ 2 * idealSiteBoxRadius α m)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (j : Fin m) (r : jets j) :
    ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j) (mixedCoveredJetCoordinates U o d z j r).1‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * (allocatedSiteJetSize (G := G) B α j * R j)) := by
  obtain ⟨hr, hi⟩ := allocatedSiteBox_mixed_coordinate_bounds B U b hR hσ S x u v hσ1 z.1 hz hsites j r
  exact mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (mul_nonneg (allocatedSiteJetSize_nonneg B α j) (hR j).le) (hchart j)
    (fun i => (z.1 j).1 i r) (fun i => ((z.1 j).2 i r : ℝ) / basisAxisScale (b j) i) hr hi

end Erdos3.VectorPolynomial

end

end OAI
