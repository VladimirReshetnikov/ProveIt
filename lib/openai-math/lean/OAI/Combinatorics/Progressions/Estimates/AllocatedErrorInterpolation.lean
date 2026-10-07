import OAI.Combinatorics.Progressions.Probability.AllocatedPrescribedRefinedDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

noncomputable def allocatedGridJetScale : ℝ :=
  ∏ a : {a // grid a}, (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1)

theorem allocatedGridJetScale_pos : 0 < allocatedGridJetScale B U b S (O := O) :=
  Finset.prod_pos (fun a _ => pow_pos
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast (allocatedGridAxisScale_bounds B U b S a).1)) _)

theorem allocatedGridLongJetScale_product :
    allocatedGridJetScale B U b S (O := O) * longScale =
      ∏ j, (∏ i, (basisAxisScale (b j) i : ℝ)) ^ Fintype.card (O j) := by
  let f : LayerSamplerAxis I n → ℝ := fun a =>
    match a with
    | ⟨_, .inl _⟩ => 1
    | ⟨j, .inr i⟩ => (basisAxisScale (b j) i : ℝ) ^ Fintype.card (O j)
  have hg : (∏ a : {a // grid a}, f a.val) = allocatedGridJetScale B U b S (O := O) := by
    apply Finset.prod_congr rfl
    intro a _
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · rfl
  have hl : (∏ a : {a // ¬grid a}, f a.val) = longScale := by
    apply Finset.prod_congr rfl
    intro a _
    rcases a with ⟨⟨j, i | i⟩, ha⟩ <;> rfl
  rw [← hg, ← hl, Fintype.prod_subtype_mul_prod_subtype]
  change (∏ a : Σ j, I j ⊕ Fin (n j), f a) = _
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fintype.prod_sum_type]
  simp only [f, Finset.prod_const_one, one_mul, Finset.prod_pow]

theorem allocatedGridLongJetScale_covolume :
    (allocatedGridJetScale B U b S (O := O) * longScale * coveredJetArrayScale (O := O) U)⁻¹ =
      ∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j) := by
  rw [allocatedGridLongJetScale_product, coveredJetArrayScale, ← Finset.prod_mul_distrib,
    ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← mul_pow, ← inv_pow, mul_inv_rev, inv_inv, mixedDensityCovolumeRatio, div_eq_mul_inv]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

theorem allocatedCoefficientError_interpolation (η : ℝ)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (r : ∀ j, O j → Q j → ZMod d) :
    allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z r * (η / longScale) =
      η * coefficientDeckJetDensity
        (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) rows d r *
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j)) *
      allocatedGridJetInterpolation B U b S hR hσ x u v rows
        (allocatedGridNormalizedRows B U b S (fun a => coefficientJetAxisEquiv O I n z a.val)) := by
  rw [allocatedGridJetInterpolation_grid, ← allocatedGridLongJetScale_covolume B U b S]
  change (_ * _ / coveredJetArrayScale (O := O) U) * (η / longScale) =
    η * _ * (allocatedGridJetScale B U b S (O := O) * longScale * coveredJetArrayScale (O := O) U)⁻¹ *
      (allocatedGridJetScale B U b S (O := O) * _)
  have hg := (allocatedGridJetScale_pos B U b S (O := O)).ne'
  have hl : longScale ≠ 0 := (Finset.prod_pos
    (fun a _ => allocatedLongJetOutputScale_pos B U b S (O := O) a)).ne'
  have hc := (coveredJetArrayScale_pos (O := O) U).ne'
  field_simp

end Erdos3.VectorPolynomial

end

end OAI
