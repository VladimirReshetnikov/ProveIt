/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedCoveredComparison
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedEndpointIdentity
import OAI.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

noncomputable def allocatedIdealSiteCoordinates
    (z : AllocatedLongJetRows B U b S jets) : Finset α → LayerSamplerAxis I n → ℝ :=
  realSitesFromBoundedJets (fun a : LayerSamplerAxis I n => (a.1 : ℕ) + 1) (fun q =>
    if ha : ¬grid q.1 then
      allocatedLongJetRealCoordinates B U b S z ⟨⟨q.1, ha⟩, q.2⟩ / R q.1.1
    else 0)

theorem allocatedIdealSiteCoordinates_jet
    (z : AllocatedLongJetRows B U b S jets) (a : {a // ¬grid a}) (r : jets a.val.1) :
    booleanCoefficient (fun s => allocatedIdealSiteCoordinates B U b S z s a.val) r.val =
      allocatedLongJetRealCoordinates B U b S z ⟨a, r⟩ / R a.val.1 := by
  unfold allocatedIdealSiteCoordinates realSitesFromBoundedJets
  rw [realBoundedSiteReconstruction_coefficient]
  simp only [dite_eq_left a.property]

theorem allocatedIdealSiteCoordinates_physical_jets (hR : ∀ j, 0 < R j)
    (z : AllocatedLongJetRows B U b S jets) :
    booleanSiteJets (fun a : {a // ¬grid a} =>
      (Subtype.val : jets a.val.1 → Finset α))
      (fun s a => R a.val.1 * allocatedIdealSiteCoordinates B U b S z s a.val) =
      allocatedLongJetRealCoordinates B U b S z := by
  funext q
  change booleanCoefficient (fun s => R q.1.val.1 * allocatedIdealSiteCoordinates B U b S z s q.1.val)
    q.2.val = _
  rw [booleanCoefficient_const_mul, allocatedIdealSiteCoordinates_jet]
  field_simp [(hR q.1.val.1).ne']

theorem allocatedIdealSiteCoordinates_density (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (z : AllocatedLongJetRows B U b S jets) :
    (∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1) *
      physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) =
      activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α)) δ
        (booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
          (fun s a => allocatedIdealSiteCoordinates B U b S z s a.val)) := by
  have h := physicalActiveProfileIdeal_normalized_sites (G := G) (Z := G × Option α) (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1)
    hLayer grid (fun a => (Subtype.val : jets a.val.1 → Finset α))
    (fun a => R a.1) (fun a => hR a.1) δ (allocatedIdealSiteCoordinates B U b S z)
  rw [allocatedIdealSiteCoordinates_physical_jets B U b S hR z] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

theorem allocatedIdealSiteCoordinates_bound_of_ne_zero
    (hR : ∀ j, 0 < R j) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (z : AllocatedLongJetRows B U b S jets)
    (hne : physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
      (fun a => (Subtype.val : jets a.val.1 → Finset α))
      (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) ≠ 0)
    (s : Finset α) (a : LayerSamplerAxis I n) :
    |allocatedIdealSiteCoordinates B U b S z s a| ≤
      (2 : ℝ) ^ Fintype.card α * (partitionedIdealRadius α m + 1) := by
  let v : (Σ a : {a // ¬grid a}, jets a.val.1) → ℝ :=
    fun q => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1
  have hactive : activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
      (fun a => (Subtype.val : jets a.val.1 → Finset α)) δ v ≠ 0 := by
    intro hz
    apply hne
    rw [physicalActiveProfileIdeal_eq]
    change _ * activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
      (fun a => (Subtype.val : jets a.val.1 → Finset α)) δ v = 0
    rw [hz, mul_zero]
  have hv : ‖v‖ ≤ partitionedIdealRadius α m + 1 := by
    apply le_of_not_gt
    intro hv
    exact hactive (activeAveragedProfileIdeal_zero_outside (G × Option α) hLayer grid
      (fun a => (Subtype.val : jets a.val.1 → Finset α))
      (fun a => Nat.succ_le_of_lt a.1.isLt) δ hδ hδ1 v hv)
  have hrad : 0 ≤ partitionedIdealRadius α m + 1 := by
    have h := partitionedIdealRadius_nonneg α m
    linarith
  unfold allocatedIdealSiteCoordinates
  apply realSitesFromBoundedJets_bound (fun a : LayerSamplerAxis I n => (a.1 : ℕ) + 1) _ hrad
  intro q
  split_ifs with ha
  · simpa only [abs_zero] using hrad
  · have hcoord : |v ⟨⟨q.1, ha⟩, q.2⟩| ≤ ‖v‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v ⟨⟨q.1, ha⟩, q.2⟩
    exact hcoord.trans hv

theorem allocatedIdealSiteCoordinates_zero_outside
    (hR : ∀ j, 0 < R j) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (z : AllocatedLongJetRows B U b S jets) (s : Finset α) (a : LayerSamplerAxis I n)
    (hlarge : (2 : ℝ) ^ Fintype.card α * (partitionedIdealRadius α m + 1) <
      |allocatedIdealSiteCoordinates B U b S z s a|) :
    physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
      (fun a => (Subtype.val : jets a.val.1 → Finset α))
      (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) = 0 := by
  by_contra hne
  exact (not_lt_of_ge (allocatedIdealSiteCoordinates_bound_of_ne_zero B U b S hR δ hδ hδ1 z hne s a)) hlarge

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin 1) (Fin.val j + 1))
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

noncomputable def allocatedOneCubeFullLongJets (z : AllocatedLongJetRows B U basis S jets) : Jet → ℝ :=
  fun q => allocatedLongJetRealCoordinates B U basis S z
    ⟨q.1, oneCubeBoundedJetEquiv (q.1.val.1.val + 1) (Nat.le_add_left 1 _) q.2⟩

theorem allocatedOneCubeNormalizedSites_eq (z : AllocatedLongJetRows B U basis S jets) :
    oneCubeNormalizedSites grid (fun a => R a.1) (allocatedOneCubeFullLongJets B U basis S z) =
      allocatedIdealSiteCoordinates B U basis S z := by
  exact oneCubeNormalizedSites_bounded_coordinates grid (fun a => R a.1)
    (fun a : LayerSamplerAxis I n => a.1.val + 1) (fun a => Nat.le_add_left 1 _)
    (allocatedLongJetRealCoordinates B U basis S z)

end Erdos3.VectorPolynomial

end

end OAI
