import OAI.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowMap" => (fun j : Fin m => (Subtype.val : rows j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rows I n grid

noncomputable def allocatedKernelSiteLift (period : ℕ)
    (r : Finset α → ∀ j, Fin (n j) → ZMod period) : AllocatedLongJetRows B U b S rows
  | ⟨⟨_, .inl _⟩, _⟩ => fun _ => 0
  | ⟨⟨j, .inr i⟩, _⟩ => fun t => (booleanCoefficient (fun s => r s j i) t.val).val

variable (x : G → IntegerScalarCubeBox α S.value) (modulus : ℕ)
variable (residue : ∀ j, Matrix {t : Finset α // t ∈ rowSets j}
  (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

noncomputable def allocatedKernelSiteMask (period : ℕ)
    (r : Finset α → ∀ j, Fin (n j) → ZMod period) : ℝ :=
  ∏ a, allocatedLongJetMask B U b S x rowMap modulus residue a
    (allocatedKernelSiteLift B U b S rowSets period r a)

variable {Q : Fin m → Type*}

theorem allocatedKernelSiteMask_reconstructed (period : ℕ) [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (rows j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rowMap j)).mulVecLin.range)
    (d : ℕ) (z : MixedCoveredJetSource I rows Q n d) :
    allocatedKernelSiteMask B U b S rowSets x modulus residue period
      (fun s j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period)) =
      ∏ a, allocatedLongJetMask B U b S x rowMap modulus residue a ((split z.1).2 a) := by
  unfold allocatedKernelSiteMask
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · rfl
  · change coefficientResidueMultiplier _ (residue j) _ =
      coefficientResidueMultiplier _ (residue j) ((z.1 j).2 i)
    apply coefficientResidueMultiplier_eq_of_output_residue _ _ period (hperiod j)
    funext t
    change (((booleanCoefficient (fun s =>
      (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period)) t.val).val : ℤ) :
        ZMod period) = ((z.1 j).2 i t : ZMod period)
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, mixedCoveredRowsSiteValue_integer]
    have h := booleanCoefficient_map (Int.castRingHom (ZMod period))
      (integerBooleanSitesFromRows (rowSets j) ((z.1 j).2 i)) t.val
    rw [integerBooleanSitesFromRows_coefficient_mem] at h
    exact h.symm

omit [Fintype α] in
theorem allocatedKernelSiteMask_bound (period : ℕ)
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rowMap j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rowMap j modulus (residue j) z ≤ C)
    (r : Finset α → ∀ j, Fin (n j) → ZMod period) :
    |allocatedKernelSiteMask B U b S rowSets x modulus residue period r| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) :=
  allocatedLongJetMask_product_bound B U b S x rowMap modulus residue hC hm _

theorem allocatedLongProfileDensity_site_mask (period : ℕ) [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (rows j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rowMap j)).mulVecLin.range)
    (d : ℕ) (f : ((Σ a : {a // ¬grid a}, rows a.val.1) → ℝ) → ℝ)
    (z : MixedCoveredJetSource I rows Q n d) :
    allocatedLongProfileDensity B U b S x rowMap modulus residue f ((split z.1).2) =
      allocatedKernelSiteMask B U b S rowSets x modulus residue period
        (fun s j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period)) *
      f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
        (∏ a, allocatedLongJetOutputScale B U b S (O := rows) a) := by
  rw [allocatedLongProfileDensity,
    allocatedKernelSiteMask_reconstructed B U b S rowSets x modulus residue period hperiod d z]

theorem allocatedKernelSiteMask_expansion (period : ℕ) [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (rows j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rowMap j)).mulVecLin.range)
    (d : ℕ) {T : Type*} [Fintype T] (c : T → ℂ)
    (f : T → Finset α → MixedCoveredJetSource I (fun _ => Unit) Q n d → ℂ)
    (z : MixedCoveredJetSource I rows Q n d) :
    ((∏ a, allocatedLongJetMask B U b S x rowMap modulus residue a ((split z.1).2 a) : ℝ) : ℂ) *
      (∑ k, c k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s)) =
    ∑ r : Finset α → ∀ j, Fin (n j) → ZMod period, ∑ k,
      ((allocatedKernelSiteMask B U b S rowSets x modulus residue period r : ℂ) * c k) *
        ∏ s, maskedSiteFactor (fun _ v j i => ((v.1 j).2 i () : ZMod period)) r f k s
          (mixedCoveredRowsSiteValue rowSets d z s) := by
  rw [maskedSiteExpansion_identity,
    allocatedKernelSiteMask_reconstructed B U b S rowSets x modulus residue period hperiod d z]

theorem allocatedKernelSiteMask_coefficient_sum (period : ℕ) [NeZero period]
    {C A : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rowMap j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rowMap j modulus (residue j) z ≤ C)
    {T : Type*} [Fintype T] (c : T → ℂ) (hc : (∑ k, ‖c k‖) ≤ A) :
    (∑ r : Finset α → ∀ j, Fin (n j) → ZMod period, ∑ k,
      ‖(allocatedKernelSiteMask B U b S rowSets x modulus residue period r : ℂ) * c k‖) ≤
      (Fintype.card (∀ j, Fin (n j) → ZMod period) : ℝ) ^ Fintype.card (Finset α) *
        C ^ Fintype.card (LayerSamplerAxis I n) * A := by
  apply maskedSiteExpansion_coefficient_sum _ c (pow_nonneg (zero_le_one.trans hC) _) _ hc
  intro r
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact allocatedKernelSiteMask_bound B U b S rowSets x modulus residue period hC hm r

end Erdos3.VectorPolynomial

end

end OAI
