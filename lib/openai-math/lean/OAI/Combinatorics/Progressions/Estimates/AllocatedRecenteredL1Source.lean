import OAI.Combinatorics.Progressions.Dynamics.PhysicalRowsBudgetedL1Perturbation
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalExponentialCover

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem finiteWeightedComplex_norm_sq_le {A : Type*} [Fintype A] (c f : A → ℂ) :
    ‖∑ a, c a * f a‖ ^ 2 ≤ (∑ a, ‖c a‖) * ∑ a, ‖c a‖ * ‖f a‖ ^ 2 := by
  have hn : ‖∑ a, c a * f a‖ ≤ ∑ a, ‖c a‖ * ‖f a‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun a => c a * f a)
  apply (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun a _ => norm_nonneg (c a))
    (fun a _ => mul_nonneg (norm_nonneg (c a)) (sq_nonneg ‖f a‖))
    (fun a _ => by ring_nf; exact le_refl _)

theorem finiteSource_real_le_of_square_perturbation {A : Type*} [Fintype A]
    (c f g : A → ℂ) {κ W E δ : ℝ}
    (hsource : κ ≤ (∑ a, c a * f a).re)
    (hmass : (∑ a, ‖c a‖) ≤ W)
    (herror : (∑ a, ‖c a‖ * ‖f a - g a‖ ^ 2) ≤ E)
    (hδ : 0 ≤ δ) (hcost : W * E ≤ δ ^ 2) :
    κ - δ ≤ (∑ a, c a * g a).re := by
  have hn := finiteWeightedComplex_norm_sq_le c (fun a => f a - g a)
  have hprod := mul_le_mul hmass herror
    (Finset.sum_nonneg (fun a _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))
    ((Finset.sum_nonneg (fun a _ => norm_nonneg _)).trans hmass)
  have hnorm : ‖∑ a, c a * (f a - g a)‖ ≤ δ :=
    (sq_le_sq₀ (norm_nonneg _) hδ).mp (hn.trans (hprod.trans hcost))
  simp only [mul_sub, Finset.sum_sub_distrib] at hnorm
  have hr := (Complex.re_le_norm ((∑ a, c a * f a) - ∑ a, c a * g a)).trans hnorm
  rw [Complex.sub_re] at hr
  linarith

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
local notation "Cube" => (X → (Unit ⊕ Fin dim) → ℤ)
local notation "window" => spatialWindow (α := Fin dim) H 4
local notation "scale" => ((∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) Lsp i) : ℝ)
local notation "factor" => (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
local notation "reconstruct" => (fun a : cells => physicalResidueReconstruction root D base
  (boundedColumnResidueRepresentative stride (Subtype.val a)) stride)
local notation "target" a => columnResiduePattern stride
  (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride a)))
local notation "V₁" => referenceJetEnvelopeWidths (q := dim) stride H

include hs hV hZ hH hT hLsp hsc hrows hprofile in
theorem physicalReconstruction_weighted_sampled_error
    (ψ test : Cube → ℂ) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ window, ‖ψ w‖ ≤ Cψ) (htest : ∀ w, ‖test w‖ ≤ 1)
    (error : Cube → ℝ) (he0 : ∀ w, 0 ≤ error w) {E : ℝ}
    (he : ∀ a : cells,
      (0 < ∑' z, selectedResidueSmoothWeight stride {target a.val} V₁ z) ∧
      selectedResidueDensityMass stride {target a.val} V₁
        (fun z => error (translatePhysicalCube base (standardPhysicalCubeOutput z))) ≤ E) :
    (∑ t : cells × window,
      ‖(selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val)‖ * error (reconstruct t.1 t.2.val)) ≤ Cψ * (factor * E) := by
  have hscale : 0 < scale := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hH x) (hT x) hLsp i))
  have hmass (a : cells) : (∑ w ∈ window, error (reconstruct a w)) ≤ (factor * E) * scale := by
    have hv := referenceJetEnvelopeWidths_pos (q := dim) stride hs H hH
    have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root D a.val H hH hrows hprofile
      (fun w => error (translatePhysicalCube base w)) (fun w => he0 _) (he a).1
    have hvol := referenceJetEnvelope_anisotropic_volume (q := dim) stride hs H T hLsp.ne' hsc
    have hvol0 : 0 ≤ (3 / 2 : ℝ) ^ Fintype.card (Option (Fin dim) × X) *
        (∏ i, residueProfileWidth stride V₁ i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) :=
      div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (Finset.prod_nonneg (fun i _ => (residueProfileWidth_pos stride V₁ hs hv i).le)))
        (pow_pos smoothProbabilityProfile_pos_zero _).le
    have hh := hraw.trans (mul_le_mul_of_nonneg_left (he a).2 hvol0)
    rw [hvol] at hh
    simp_rw [← physicalResidueReconstruction_translate root D base] at hh
    exact hh.trans_eq (by ring)
  exact selectedResidue_coefficient_tail_of_window_mass stride cells V hV hZ window ψ
    (fun a w => test (reconstruct a w)) (fun a w => error (reconstruct a w))
    hscale hCψ hψ (fun _ w => htest _) (fun _ w => he0 _) hmass

include hs hV hZ hH hT hLsp hsc hrows hprofile in
theorem physicalReconstruction_source_of_sampled_square
    (ψ test f g : Cube → ℂ) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ window, ‖ψ w‖ ≤ Cψ) (htest : ∀ w, ‖test w‖ ≤ 1)
    {E κ δ : ℝ}
    (he : ∀ a : cells,
      (0 < ∑' z, selectedResidueSmoothWeight stride {target a.val} V₁ z) ∧
      selectedResidueDensityMass stride {target a.val} V₁
        (fun z => ‖f (translatePhysicalCube base (standardPhysicalCubeOutput z)) -
          g (translatePhysicalCube base (standardPhysicalCubeOutput z))‖ ^ 2) ≤ E)
    (hsource : κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) * f (reconstruct t.1 t.2.val)).re)
    (hδ : 0 ≤ δ) (hcost : (Cψ * ((Finset.card window : ℝ) / scale)) * (Cψ * (factor * E)) ≤ δ ^ 2) :
    κ - δ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) * g (reconstruct t.1 t.2.val)).re := by
  have herr := physicalReconstruction_weighted_sampled_error stride hs root D base cells V hV hZ
    H T hH hT hLsp hsc hrows hprofile ψ test hCψ hψ htest
    (fun w => ‖f w - g w‖ ^ 2) (fun _ => sq_nonneg _) he
  have hscale : 0 < scale := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hH x) (hT x) hLsp i))
  have hmass := selectedResidue_coefficient_tail stride cells V hV hZ window ψ
    (fun a w => test (reconstruct a w)) (fun _ _ => (1 : ℝ)) hscale hCψ zero_le_one
    hψ (fun _ w => htest _) (fun _ _ => le_rfl)
    (show (Finset.card window : ℝ) ≤ ((Finset.card window : ℝ) / scale) * scale by
      rw [div_mul_cancel₀ _ hscale.ne'])
  simp only [mul_one] at hmass
  exact finiteSource_real_le_of_square_perturbation _ _ _ hsource hmass herr hδ hcost

include hs hV hZ hH hT hLsp hsc hrows hprofile in
theorem physicalReconstruction_source_of_sampled_square_geometric
    (ψ test f g : Cube → ℂ) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ window, ‖ψ w‖ ≤ Cψ) (htest : ∀ w, ‖test w‖ ≤ 1)
    {E κ δ : ℝ}
    (he : ∀ a : cells,
      (0 < ∑' z, selectedResidueSmoothWeight stride {target a.val} V₁ z) ∧
      selectedResidueDensityMass stride {target a.val} V₁
        (fun z => ‖f (translatePhysicalCube base (standardPhysicalCubeOutput z)) -
          g (translatePhysicalCube base (standardPhysicalCubeOutput z))‖ ^ 2) ≤ E)
    (hsource : κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) * f (reconstruct t.1 t.2.val)).re)
    (hδ : 0 ≤ δ) (hH1 : ∀ x, 1 ≤ H x)
    (hcost : (Cψ * ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X)) * (Cψ * (factor * E)) ≤ δ ^ 2) :
    κ - δ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) * g (reconstruct t.1 t.2.val)).re := by
  have herr := physicalReconstruction_weighted_sampled_error stride hs root D base cells V hV hZ
    H T hH hT hLsp hsc hrows hprofile ψ test hCψ hψ htest
    (fun w => ‖f w - g w‖ ^ 2) (fun _ => sq_nonneg _) he
  have hscale : 0 < scale := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hH x) (hT x) hLsp i))
  have hmass := selectedResidue_coefficient_tail stride cells V hV hZ window ψ
    (fun a w => test (reconstruct a w)) (fun _ _ => (1 : ℝ)) hscale hCψ zero_le_one
    hψ (fun _ w => htest _) (fun _ _ => le_rfl)
    (show (Finset.card window : ℝ) ≤
      ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
        (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X) * scale by
      simpa only [Fintype.card_fin, show (2 * (4 : ℝ) + 1) = 9 by norm_num] using
        spatialWindow_card_anisotropic (α := Fin dim) H T hH1 (by norm_num : (0 : ℝ) ≤ 4) hLsp.ne' hsc)
  simp only [mul_one] at hmass
  exact finiteSource_real_le_of_square_perturbation _ _ _ hsource hmass herr hδ hcost

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
local notation "Cube" => (X → (Unit ⊕ Fin dim) → ℤ)
local notation "window" => spatialWindow (α := Fin dim) H 4
local notation "scale" => ((∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) Lsp i) : ℝ)
local notation "factor" => (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
local notation "reconstruct" => (fun a : cells => physicalResidueReconstruction root D base
  (boundedColumnResidueRepresentative stride (Subtype.val a)) stride)
local notation "target" a => columnResiduePattern stride
  (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride a)))
local notation "V₁" => referenceJetEnvelopeWidths (q := dim) stride H

include hs hV hZ hH hT hLsp hsc hrows hprofile in
theorem physicalReconstruction_source_of_sampled_l1_and_uniform
    (ψ test f ideal model : Cube → ℂ) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ window, ‖ψ w‖ ≤ Cψ) (htest : ∀ w, ‖test w‖ ≤ 1)
    {E κ ε : ℝ} (hε : 0 ≤ ε) (hH1 : ∀ x, 1 ≤ H x)
    (he : ∀ a : cells,
      (0 < ∑' z, selectedResidueSmoothWeight stride {target a.val} V₁ z) ∧
      selectedResidueDensityMass stride {target a.val} V₁
        (fun z => ‖f (translatePhysicalCube base (standardPhysicalCubeOutput z)) -
          ideal (translatePhysicalCube base (standardPhysicalCubeOutput z))‖) ≤ E)
    (happrox : ∀ w, ‖ideal w - model w‖ ≤ ε)
    (hsource : κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) * f (reconstruct t.1 t.2.val)).re) :
    κ - Cψ * (factor * E + ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X) * ε) ≤
      (∑ t : cells × window,
        (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
          test (reconstruct t.1 t.2.val) * model (reconstruct t.1 t.2.val)).re := by
  let c := fun t : cells × window =>
    (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
      test (reconstruct t.1 t.2.val)
  let W := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
    (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
  have herr := physicalReconstruction_weighted_sampled_error stride hs root D base cells V hV hZ
    H T hH hT hLsp hsc hrows hprofile ψ test hCψ hψ htest
    (fun w => ‖f w - ideal w‖) (fun _ => norm_nonneg _) he
  have hscale : 0 < scale := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hH x) (hT x) hLsp i))
  have hmass := selectedResidue_coefficient_tail stride cells V hV hZ window ψ
    (fun a w => test (reconstruct a w)) (fun _ _ => (1 : ℝ)) hscale hCψ zero_le_one
    hψ (fun _ w => htest _) (fun _ _ => le_rfl)
    (show (Finset.card window : ℝ) ≤ W * scale by
      simpa only [W, Fintype.card_fin, show (2 * (4 : ℝ) + 1) = 9 by norm_num] using
        spatialWindow_card_anisotropic (α := Fin dim) H T hH1 (by norm_num : (0 : ℝ) ≤ 4) hLsp.ne' hsc)
  simp only [mul_one] at hmass
  have herror : (∑ t : cells × window, ‖c t‖ *
      ‖f (reconstruct t.1 t.2.val) - model (reconstruct t.1 t.2.val)‖) ≤
      Cψ * (factor * E + W * ε) := by
    calc
      _ ≤ ∑ t : cells × window, ‖c t‖ *
          (‖f (reconstruct t.1 t.2.val) - ideal (reconstruct t.1 t.2.val)‖ + ε) := by
        apply Finset.sum_le_sum
        intro t _
        exact mul_le_mul_of_nonneg_left
          ((norm_sub_le_norm_sub_add_norm_sub _ (ideal (reconstruct t.1 t.2.val)) _).trans
            (add_le_add le_rfl (happrox _))) (norm_nonneg _)
      _ = (∑ t : cells × window, ‖c t‖ *
          ‖f (reconstruct t.1 t.2.val) - ideal (reconstruct t.1 t.2.val)‖) +
          (∑ t : cells × window, ‖c t‖) * ε := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ Cψ * (factor * E) + (Cψ * W) * ε :=
        add_le_add herr (mul_le_mul_of_nonneg_right hmass hε)
      _ = _ := by ring
  have hn : ‖∑ t : cells × window, c t *
      (f (reconstruct t.1 t.2.val) - model (reconstruct t.1 t.2.val))‖ ≤
      Cψ * (factor * E + W * ε) := by
    exact (norm_sum_le _ _).trans (by simpa only [norm_mul] using herror)
  simp only [mul_sub, Finset.sum_sub_distrib] at hn
  have hr := (Complex.re_le_norm _).trans hn
  rw [Complex.sub_re] at hr
  change κ ≤ (∑ t : cells × window, c t * f (reconstruct t.1 t.2.val)).re at hsource
  change κ - Cψ * (factor * E + W * ε) ≤ _
  linarith only [hr, hsource]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
local notation "Cube" => (X → (Unit ⊕ Fin dim) → ℤ)
local notation "window" => spatialWindow (α := Fin dim) H 4
local notation "scale" => ((∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) Lsp i) : ℝ)
local notation "factor" => (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
local notation "reconstruct" => (fun a : cells => physicalResidueReconstruction root D base
  (boundedColumnResidueRepresentative stride (Subtype.val a)) stride)
local notation "target" a => columnResiduePattern stride
  (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride a)))
local notation "V₁" => referenceJetEnvelopeWidths (q := dim) stride H

include hs hV hZ hH hT hLsp hsc hrows hprofile in

theorem physicalReconstruction_source_of_haar_l1_surrogate
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (s : Cube → Z) (f ideal surrogate : Z → ℂ) (model ψ test : Cube → ℂ)
    (hf : Measurable f) (hi : Measurable ideal) (hg : Measurable surrogate)
    {Cf Cg : ℝ} (hfb : ∀ z, ‖f z‖ ≤ Cf) (hgb : ∀ z, ‖surrogate z‖ ≤ Cg)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ window, ‖ψ w‖ ≤ Cψ) (htest : ∀ w, ‖test w‖ ≤ 1)
    {E δ εsample κ ε : ℝ} (hε : 0 ≤ ε) (hH1 : ∀ x, 1 ≤ H x)
    (hmass : (∫ z, ‖f z - ideal z‖ ∂μ) ≤ E)
    (happrox : ∀ z, ‖ideal z - surrogate z‖ ≤ δ)
    (he : ∀ a : cells,
      (0 < ∑' z, selectedResidueSmoothWeight stride {target a.val} V₁ z) ∧
      selectedResidueDensityMass stride {target a.val} V₁
        (fun z => ‖f (s (translatePhysicalCube base (standardPhysicalCubeOutput z))) -
          surrogate (s (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤
        (∫ z, ‖f z - surrogate z‖ ∂μ) + εsample)
    (htrunc : ∀ w, ‖ideal (s w) - model w‖ ≤ ε)
    (hsource : κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) * f (s (reconstruct t.1 t.2.val))).re) :
    κ - Cψ * (factor * (E + 2 * δ + εsample) +
      ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
        (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X) * ε) ≤
      (∑ t : cells × window,
        (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
          test (reconstruct t.1 t.2.val) * model (reconstruct t.1 t.2.val)).re := by
  apply physicalReconstruction_source_of_sampled_l1_and_uniform stride hs root D base cells V hV hZ
    H T hH hT hLsp hsc hrows hprofile ψ test (fun w => f (s w)) (fun w => ideal (s w)) model
    hCψ hψ htest hε hH1 ?_ htrunc hsource
  intro a
  obtain ⟨hZa, hsample⟩ := he a
  refine ⟨hZa, ?_⟩
  exact selectedResidueDensityMass_l1_surrogate μ stride {target a.val} V₁
    (referenceJetEnvelopeWidths_pos stride hs H hH) hZa
    (fun z => s (translatePhysicalCube base (standardPhysicalCubeOutput z))) f ideal surrogate
    hf hi hg hfb hgb happrox hmass hsample

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_translated_physical_jet_l1_perturbation (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hLg : (Lg : ℝ) ≤ Real.exp T)
    (_hCf : (Cf : ℝ) ≤ Real.exp T) (_hCg : (Cg : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T)
    (ideal : EuclideanJetLayers U O → ℂ) (_hi : Measurable ideal)
    {δ : ℝ} (_happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δ)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))) -
          ideal (physicalCubeRowSample U q rows p _hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ E + 2 * δ + (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_physical_jet_l1_perturbation_budgeted m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η hη hdim hLf hLg hCf hCg hjet hηT ideal hi δ happ E hmass
  let p' := fun j => translate (fun x => (base x : ℝ)) (p j)
  have hp' (j) : DegreeLE (1 : I → ℕ) (j.val + 1) (p' j) :=
    degreeLE_translate _ (fun _ => Nat.zero_lt_one) _ _ (hp j)
  have hm' (j) : ∀ ex, coefficients (p' j) ex ∈ U j :=
    coefficients_translate_mem (U j) _ (p j) (hm j)
  have hrank' (j) : HasLayerSamplingRank (j.val + 1) H R (U j) (p' j) :=
    (hasLayerSamplingRank_translate_iff _ _ H R (U j) (p j) (hp j)).mpr (hrank j)
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hT hn hd U μ ν p' hp' hm' q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank' hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb hη hdim hLf hLg hCf hCg hjet hηT ideal hi happ hmass
  refine ⟨hZ, ?_⟩
  have hid (z : Option (Fin dim) × I → ℤ) :
      physicalCubeRowSample U q rows p' hm' (standardPhysicalCubeOutput z) =
        physicalCubeRowSample U q rows p hm (translatePhysicalCube base (standardPhysicalCubeOutput z)) :=
    physicalCubeRowSample_translate U q rows p hm base _
  simp only [hid] at he
  exact he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_physical_rows_l1_source (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hLg : (Lg : ℝ) ≤ Real.exp T)
    (_hCf : (Cf : ℝ) ≤ Real.exp T) (_hCg : (Cg : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T)
    (ideal : EuclideanJetLayers U O → ℂ) (_hi : Measurable ideal)
    {δ : ℝ} (_happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δ)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∀ {K : Type*} [Fintype K]
      (root : K → ℤ) (D : Matrix (Fin dim) K ℤ)
      (cells : Finset (ColumnResiduePattern (Option K) I stride))
      (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z)
      (_hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (Hsp Tsp : I → ℝ) (_hHsp : ∀ i, 0 < Hsp i) (_hTsp : ∀ i, 0 < Tsp i)
      {Wsp Lsp : ℝ} (_hLsp : 0 < Lsp) (_hsc : ∀ i, Hsp i = (1 + Wsp) * Tsp i)
      (_hrowsize : ∀ i a, (∑ k, |(physicalCubeCoefficient root D a k : ℝ)|) ≤ Hsp i)
      (_hprofile : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hsp i)
      (_hH1 : ∀ i, 1 ≤ Hsp i)
      (_hwidth : ∀ z, ρ * H z.2 ≤ referenceJetEnvelopeWidths (q := dim) stride Hsp z),
    let window := spatialWindow (α := Fin dim) Hsp 4
    let scale : ℝ := ∏ i, ∏ a, physicalSpatialOutputScale (Fin dim) (Hsp i) (Tsp i) Lsp a
    let reconstruct := fun a : cells => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative stride a.val) stride
    let point := physicalCubeRowSample U q rows p _hm
    ∀ (ψ test : (I → (Unit ⊕ Fin dim) → ℤ) → ℂ) (model : EuclideanJetLayers U O → ℂ)
      {Cψ κ εtrunc : ℝ} (_hCψ : 0 ≤ Cψ)
      (_hψ : ∀ w ∈ window, ‖ψ w‖ ≤ Cψ) (_htest : ∀ w, ‖test w‖ ≤ 1)
      (_hεtrunc : 0 ≤ εtrunc) (_htrunc : ∀ y, ‖ideal y - model y‖ ≤ εtrunc),
      κ ≤ (∑ t : cells × window, (selectedResidueCellWeight stride cells V t.1 : ℂ) *
        (ψ t.2.val / (scale : ℂ)) * test (reconstruct t.1 t.2.val) *
        f (coveredJetAmbientTorus U 1 (point (reconstruct t.1 t.2.val)))).re →
      κ - Cψ * (((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I) *
        (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card I) * (E + 2 * δ + (2 * η + ε)) +
        ((9 : ℝ) ^ Fintype.card (I × (Unit ⊕ Fin dim)) *
          (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card I) * εtrunc) ≤
        (∑ t : cells × window, (selectedResidueCellWeight stride cells V t.1 : ℂ) *
          (ψ t.2.val / (scale : ℂ)) * test (reconstruct t.1 t.2.val) *
          model (point (reconstruct t.1 t.2.val))).re := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_l1_perturbation m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR
    f g Lf Lg Cf Cg hf hg hfb hgb η hη hdim hLf hLg hCf hCg hjet hηT ideal hi δ happ E hmass
    K _ root D cells V hV hZ Hsp Tsp hHsp hTsp Wsp Lsp hLsp hsc hrowsize hprofile hH1 hwidth
    window scale reconstruct point ψ test model Cψ κ εtrunc hCψ hψ htest hεtrunc htrunc hsource
  apply physicalReconstruction_source_of_sampled_l1_and_uniform stride hs root D base cells V hV hZ
    Hsp Tsp hHsp hTsp hLsp hsc hrowsize hprofile ψ test
    (fun w => f (coveredJetAmbientTorus U 1 (point w))) (fun w => ideal (point w))
    (fun w => model (point w)) hCψ hψ htest hεtrunc hH1 ?_ (fun w => htrunc _) hsource
  intro a
  let target := columnResiduePattern stride (standardPhysicalCubeFrame
    (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride a.val)))
  obtain ⟨hZa, he⟩ := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR {target} (Finset.singleton_nonempty _)
    (referenceJetEnvelopeWidths (q := dim) stride Hsp)
    (referenceJetEnvelopeWidths_pos stride hs Hsp hHsp) hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb hη hdim hLf hLg hCf hCg hjet hηT ideal hi happ hmass
  exact ⟨hZa, he⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

theorem allocatedRecenteredSelectedMean_l1_source
    (law : FiniteProbabilityWeights fullTuple) (r : labels)
    (hlabel : ∀ y, law.weight y ≠ 0 → principalResidueLabel refined y = r)
    (hwhole : principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (ideal model : EuclideanJetLayers U O → ℂ)
    (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (htest : ∀ w, ‖test w‖ ≤ 1) {κ δ Eerror ε : ℝ}
    (hsource : κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)).re)
    (hε : 0 ≤ ε) (htrunc : ∀ z, ‖ideal z - model z‖ ≤ ε) :
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r)
    let D := allocatedPhysicalCubeDirections B U b S x (wholeReference r)
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let V₁ := referenceJetEnvelopeWidths (q := dim) q H
    let _A := (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i : ℝ)
    let C := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight q cells V z) →
    (∀ t i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    (∀ t, 1 ≤ H t) →
    (∀ a : cells,
      let target := columnResiduePattern q (standardPhysicalCubeFrame
        (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative q a.val)))
      (0 < ∑' z, selectedResidueSmoothWeight q {target} V₁ z) ∧
      selectedResidueDensityMass q {target} V₁ (fun z =>
        ‖law.complexMean (fun y => profile y (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))) -
          ideal (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ Eerror) →
    C * (volumeFactor * Eerror + ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X) * ε) ≤ δ →
    κ - δ ≤
      (∑ t : cells × window, (selectedResidueCellWeight q cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
          t.1.val t.2.val))).re := by
  intro root D H T V V₁ A C volumeFactor hV hZ hrows hprofile hH1 he hcost
  have hH (t) : 0 < H t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
  have hT (t) : 0 < T t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2
  let ψ := allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh
    (principalResidueLabel modulus (wholeReference r))
  have hC : 0 ≤ C := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg _)))) _
  have hψ : ∀ v ∈ window, ‖ψ v‖ ≤ C :=
    allocatedResidueSpatialKernel_norm_le B U b S x X hM selection hx modulus H hW mesh
      hH hbudget hmesh hperiod (principalResidueLabel modulus (wholeReference r))
  have hid := allocatedRecenteredProfileTerm_selected_mean (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test
    law r hlabel hwhole profile
  have hsource' : κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
        test (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative q t.1.val) q t.2.val) *
        law.complexMean (fun y => profile y (point
          (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative q t.1.val) q t.2.val)))).re := by
    rw [hid] at hsource
    rw [Fintype.sum_prod_type]
    convert hsource using 1
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, ← Finset.sum_coe_sort window]
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [allocatedRecenteredResidueWeight, allocatedWholeResidueReconstruction, ψ, A, root, D, H, T]
    ring
  have ht := physicalReconstruction_source_of_sampled_l1_and_uniform q hq root D base cells V hV hZ H T hH hT
    (Nat.cast_pos.mpr S.positive) (trimmedSpatial_scale_ratio hW N q) hrows hprofile
    ψ test (fun w => law.complexMean (fun y => profile y (point w)))
    (fun w => ideal (point w)) (fun w => model (point w))
    hC hψ htest hε hH1 he (fun w => htrunc _) hsource'
  have ht' := (sub_le_sub_left hcost κ).trans ht
  convert ht' using 1
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  dsimp only [allocatedRecenteredResidueWeight, allocatedWholeResidueReconstruction, ψ, A, root, D, H, T]
  ring

end Erdos3.VectorPolynomial

end

end OAI
