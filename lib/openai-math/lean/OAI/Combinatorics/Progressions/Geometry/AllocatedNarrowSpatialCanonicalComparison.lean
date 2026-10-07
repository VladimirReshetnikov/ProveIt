/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.SelectedSingletonSmoothTestQuadrature
import OAI.Combinatorics.Progressions.Probability.CanonicalZeroSpatialInputLaw

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ) (W L : ℝ)

omit [Fintype X] in
theorem canonicalZeroSpatialInputMap_apply (hW : 0 ≤ W)
    (u : Option Zsp × X → ℝ) (x : X) :
    canonicalZeroSpatialInputMap s root D W L u ⟨x, Sum.inl ()⟩ =
      u (none, x) + (∑ j, (root j : ℝ) * u (some j, x)) / (1 + W) := by
  have hsum := selectedColumn_sum s (fun j => (root j : ℝ) * u (some j, x))
  simp only [Fintype.sum_empty, zero_add] at hsum
  unfold canonicalZeroSpatialInputMap canonicalSpatialKernelMap
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, normalizedIntegerPivot_entry,
    normalizedIntegerColumns_entry_div, Fintype.sum_sum_type, Fintype.sum_empty,
    add_zero, Fintype.sum_unique, selectedSpatialPivot, rootDifferenceMatrix, Matrix.fromBlocks_apply₁₁, Matrix.one_apply_eq,
    selectedSpatialFreeColumns, Matrix.of_apply, anisotropicSpatialScale,
    physicalSpatialOutputScale, Sum.elim_inl, Int.cast_one, one_mul,
    div_self (by linarith : (1 + W : ℝ) ≠ 0)]
  congr 1
  rw [← hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem canonicalZeroSpatialInputMap_lipschitz (hW : 0 ≤ W)
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W) :
    LipschitzWith 2 (canonicalZeroSpatialInputMap (X := X) s root D W L) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl a =>
    cases a
    rw [Real.dist_eq, canonicalZeroSpatialInputMap_apply s root D W L hW,
      canonicalZeroSpatialInputMap_apply s root D W L hW]
    have hsum : |∑ j, (root j : ℝ) * (u (some j, x) - v (some j, x))| ≤
        W * dist u v := by
      calc
        _ ≤ ∑ j, |(root j : ℝ) * (u (some j, x) - v (some j, x))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |(root j : ℝ)| * dist u v := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (show |u (some j, x) - v (some j, x)| ≤ dist u v from
              (Real.dist_eq _ _).symm ▸ dist_le_pi_dist u v (some j, x))
            (abs_nonneg _)
        _ = (∑ j, |(root j : ℝ)|) * dist u v := (Finset.sum_mul _ _ _).symm
        _ ≤ W * dist u v := mul_le_mul_of_nonneg_right hroot dist_nonneg
    have hden : 0 < 1 + W := by linarith
    have hdiv : |(∑ j, (root j : ℝ) * (u (some j, x) - v (some j, x))) /
        (1 + W)| ≤ dist u v := by
      rw [abs_div, abs_of_pos hden]
      apply (div_le_iff₀ hden).mpr
      exact hsum.trans (by nlinarith [dist_nonneg (x := u) (y := v)])
    have heq : u (none, x) + (∑ j, (root j : ℝ) * u (some j, x)) / (1 + W) -
        (v (none, x) + (∑ j, (root j : ℝ) * v (some j, x)) / (1 + W)) =
        (u (none, x) - v (none, x)) +
          (∑ j, (root j : ℝ) * (u (some j, x) - v (some j, x))) / (1 + W) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring
    rw [heq]
    have hcoord : |u (none, x) - v (none, x)| ≤ dist u v :=
      (Real.dist_eq _ _).symm ▸ dist_le_pi_dist u v (none, x)
    exact (abs_add_le _ _).trans (by norm_num; linarith)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X G T : Type*} [Fintype X] [Fintype G] [DecidableEq G] [Fintype T]
variable (s : Empty ↪ G) (root : G → ℤ) (D : Matrix Empty G ℤ) (W L : ℝ)
variable (e : (Option G × X) ↪ T)

theorem canonicalZeroSpatialInputProjection_law :
    (unitCoefficientSource T).map
      (fun u => canonicalZeroSpatialInputMap s root D W L (u ∘ e)) =
      canonicalZeroSpatialLaw (X := X) s root D W L := by
  change (unitCoefficientSource T).map
    (canonicalZeroSpatialInputMap s root D W L ∘ (fun u => u ∘ e)) = _
  rw [← Measure.map_map (canonicalZeroSpatialInputMap_measurable s root D W L)
    (unitCoefficientProjection_measurable e), unitCoefficientSource_marginal]
  exact canonicalZeroSpatialInputMap_law s root D W L

theorem canonicalZeroSpatialInputProjection_integral_complex
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ) (hφ : Measurable φ) :
    (∫ u, φ (canonicalZeroSpatialInputMap s root D W L (u ∘ e)) ∂unitCoefficientSource T) =
      ∫ y, φ y ∂canonicalZeroSpatialLaw s root D W L := by
  rw [← canonicalZeroSpatialInputProjection_law s root D W L e]
  symm
  exact integral_map_of_stronglyMeasurable
    ((canonicalZeroSpatialInputMap_measurable s root D W L).comp
      (unitCoefficientProjection_measurable e)) hφ.stronglyMeasurable

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

def canonicalZeroSpatialKernelEmbedding (G N X : Type*) :
    Option G × X ↪ Option (G ⊕ N) × X where
  toFun := fun p => (Option.map Sum.inl p.1, p.2)
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    cases a <;> cases b <;> simp_all

@[simp] theorem canonicalZeroSpatialKernelEmbedding_apply (G N X : Type*)
    (p : Option G × X) :
    canonicalZeroSpatialKernelEmbedding G N X p = (Option.map Sum.inl p.1, p.2) := rfl

def canonicalZeroSpatialNarrowInput {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) : Option (G ⊕ N) × X → ℝ :=
  fun a => match a.1 with
    | some (.inr _) => ξ * u a
    | _ => u a

@[simp] theorem canonicalZeroSpatialNarrowInput_none {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) (x : X) :
    canonicalZeroSpatialNarrowInput ξ u (none, x) = u (none, x) := rfl

@[simp] theorem canonicalZeroSpatialNarrowInput_inl {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) (g : G) (x : X) :
    canonicalZeroSpatialNarrowInput ξ u (some (.inl g), x) = u (some (.inl g), x) := rfl

@[simp] theorem canonicalZeroSpatialNarrowInput_inr {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) (n : N) (x : X) :
    canonicalZeroSpatialNarrowInput ξ u (some (.inr n), x) = ξ * u (some (.inr n), x) := rfl

theorem canonicalZeroSpatialNarrowInput_measurable {G N X : Type*} (ξ : ℝ) :
    Measurable (canonicalZeroSpatialNarrowInput (G := G) (N := N) (X := X) ξ) := by
  apply Measurable.of_eval
  rintro ⟨a, x⟩
  rcases a with _ | (g | n)
  · exact measurable_pi_apply (none, x)
  · exact measurable_pi_apply (some (Sum.inl g : G ⊕ N), x)
  · exact measurable_const.mul (measurable_pi_apply (some (Sum.inr n : G ⊕ N), x))

theorem canonicalZeroSpatialNarrowInput_kernel {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) :
    canonicalZeroSpatialNarrowInput ξ u ∘ canonicalZeroSpatialKernelEmbedding G N X =
      u ∘ canonicalZeroSpatialKernelEmbedding G N X := by
  funext a
  rcases a with ⟨a, x⟩
  cases a <;> rfl

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]
variable (s : Empty ↪ G) (sf : Empty ↪ (G ⊕ N))
  (root : G → ℤ) (principal : N → ℤ)
  (D : Matrix Empty G ℤ) (Df : Matrix Empty (G ⊕ N) ℤ) (W L : ℝ)

omit [Fintype X] in
theorem canonicalZeroSpatialPrincipal_difference (hW : 0 ≤ W)
    (u : Option (G ⊕ N) × X → ℝ) (x : X) :
    canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u ⟨x, .inl ()⟩ -
        canonicalZeroSpatialInputMap s root D W L
          (u ∘ canonicalZeroSpatialKernelEmbedding G N X) ⟨x, .inl ()⟩ =
      (∑ n, (principal n : ℝ) * u (some (.inr n), x)) / (1 + W) := by
  rw [canonicalZeroSpatialInputMap_apply sf _ Df W L hW,
    canonicalZeroSpatialInputMap_apply s root D W L hW]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, canonicalZeroSpatialKernelEmbedding_apply,
    Option.map_none, Option.map_some]
  ring

theorem canonicalZeroSpatialPrincipal_norm_le (hW : 0 ≤ W)
    (u : Option (G ⊕ N) × X → ℝ) (hu : ‖u‖ ≤ 1) :
    ‖canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u -
        canonicalZeroSpatialInputMap s root D W L
          (u ∘ canonicalZeroSpatialKernelEmbedding G N X)‖ ≤
      (∑ n, |(principal n : ℝ)|) / (1 + W) := by
  have hden : 0 < 1 + W := by linarith
  have hbound : 0 ≤ (∑ n, |(principal n : ℝ)|) / (1 + W) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hden.le
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  rintro ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl a =>
    cases a
    rw [Pi.sub_apply, canonicalZeroSpatialPrincipal_difference s sf root principal D Df W L hW,
      Real.norm_eq_abs, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      _ ≤ ∑ n, |(principal n : ℝ) * u (some (.inr n), x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n, |(principal n : ℝ)| := by
        apply Finset.sum_le_sum
        intro n _
        rw [abs_mul]
        have hn : |u (some (.inr n), x)| ≤ 1 :=
          (Real.norm_eq_abs _).symm ▸ (norm_le_pi_norm u (some (.inr n), x)).trans hu
        exact mul_le_of_le_one_right (abs_nonneg _) hn

theorem canonicalZeroSpatialPrincipal_test_error (hW : 0 ≤ W)
    (u : Option (G ⊕ N) × X → ℝ) (hu : ‖u‖ ≤ 1)
    {A : ℝ≥0} (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    (hφ : LipschitzWith A φ) :
    ‖φ (canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u) -
        φ (canonicalZeroSpatialInputMap s root D W L
          (u ∘ canonicalZeroSpatialKernelEmbedding G N X))‖ ≤
      (A : ℝ) * ((∑ n, |(principal n : ℝ)|) / (1 + W)) := by
  rw [← dist_eq_norm]
  apply (hφ.dist_le_mul _ _).trans
  rw [dist_eq_norm]
  exact mul_le_mul_of_nonneg_left
    (canonicalZeroSpatialPrincipal_norm_le s sf root principal D Df W L hW u hu) A.coe_nonneg

omit [DecidableEq G] [DecidableEq N] in
theorem canonicalZeroSpatialNarrowInput_lipschitz (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    LipschitzWith 1 (canonicalZeroSpatialNarrowInput (G := G) (N := N) (X := X) ξ) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  rintro ⟨a, x⟩
  rcases a with _ | (g | n)
  · exact dist_le_pi_dist u v (none, x)
  · exact dist_le_pi_dist u v (some (.inl g), x)
  · simp only [canonicalZeroSpatialNarrowInput_inr, Real.dist_eq, ← mul_sub,
      abs_mul, abs_of_nonneg hξ0]
    exact (mul_le_mul_of_nonneg_left (show |u (some (.inr n), x) -
      v (some (.inr n), x)| ≤ dist u v from
        (Real.dist_eq _ _).symm ▸ dist_le_pi_dist u v (some (.inr n), x)) hξ0).trans
      (mul_le_of_le_one_left dist_nonneg hξ1)

omit [Fintype X] in
theorem canonicalZeroSpatialNarrowPrincipal_difference (hW : 0 ≤ W) (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) :
    canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
        (canonicalZeroSpatialNarrowInput ξ u) -
      canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X) =
    ξ • (canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u -
      canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X)) := by
  ext ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl a =>
    cases a
    have h := canonicalZeroSpatialPrincipal_difference s sf root principal D Df W L hW
      (canonicalZeroSpatialNarrowInput ξ u) x
    rw [canonicalZeroSpatialNarrowInput_kernel] at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [h, canonicalZeroSpatialPrincipal_difference s sf root principal D Df W L hW]
    simp only [canonicalZeroSpatialNarrowInput_inr]
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring

theorem canonicalZeroSpatialNarrowPrincipal_norm_le (hW : 0 ≤ W) (ξ : ℝ) (hξ0 : 0 ≤ ξ)
    (u : Option (G ⊕ N) × X → ℝ) (hu : ‖u‖ ≤ 1) :
    ‖canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
        (canonicalZeroSpatialNarrowInput ξ u) -
      canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X)‖ ≤
      ξ * ((∑ n, |(principal n : ℝ)|) / (1 + W)) := by
  rw [canonicalZeroSpatialNarrowPrincipal_difference s sf root principal D Df W L hW ξ,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ0]
  exact mul_le_mul_of_nonneg_left
    (canonicalZeroSpatialPrincipal_norm_le s sf root principal D Df W L hW u hu) hξ0

theorem canonicalZeroSpatialNarrowPrincipal_test_error (hW : 0 ≤ W) (ξ : ℝ) (hξ0 : 0 ≤ ξ)
    (u : Option (G ⊕ N) × X → ℝ) (hu : ‖u‖ ≤ 1)
    {A : ℝ≥0} (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    (hφ : LipschitzWith A φ) :
    ‖φ (canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
        (canonicalZeroSpatialNarrowInput ξ u)) -
      φ (canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X))‖ ≤
      (A : ℝ) * (ξ * ((∑ n, |(principal n : ℝ)|) / (1 + W))) := by
  rw [← dist_eq_norm]
  apply (hφ.dist_le_mul _ _).trans
  rw [dist_eq_norm]
  exact mul_le_mul_of_nonneg_left
    (canonicalZeroSpatialNarrowPrincipal_norm_le s sf root principal D Df W L hW ξ hξ0 u hu)
    A.coe_nonneg

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {X G : Type*} [Fintype X] [Fintype G] [DecidableEq G]

theorem selectedCanonicalZeroSpatial_complex_quadrature
    (s : Empty ↪ G) (root : G → ℤ) (D : Matrix Empty G ℤ) (W L : ℝ)
    (hW : 0 ≤ W) (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (r : ColumnResiduePattern (Option G) X modulus)
    (V : Option G × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r} V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, (modulus z.2 : ℝ) / V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option G × X) *
      ((Fintype.card (Option G × X) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    {A : ℝ≥0} (hLip : LipschitzWith A φ) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus {r} V hV hZ z).toReal : ℂ) *
        φ (canonicalZeroSpatialInputMap s root D W L (fun k => (z k : ℝ) / V k))) -
      ∫ y, φ y ∂canonicalZeroSpatialLaw s root D W L‖ ≤
      4 * (4 : ℝ) ^ Fintype.card (Option G × X) *
        (2 * (A : ℝ) + 2 * ((Fintype.card (Option G × X) : ℝ) * probabilityProfileLipschitz)) * δ := by
  rw [canonicalZeroSpatialInputMap_integral_complex s root D W L φ hLip.continuous.measurable]
  have he := selectedResidueSmoothPMF_singleton_complex_quadrature modulus hmodulus r V hV hZ
    hδ hδ1 hmesh hsmall (φ ∘ canonicalZeroSpatialInputMap s root D W L)
    (hLip.comp (canonicalZeroSpatialInputMap_lipschitz s root D W L hW hroot))
    (fun u => hφ _)
  simpa only [Function.comp_apply, NNReal.coe_mul, NNReal.coe_ofNat, mul_comm (A : ℝ) 2] using he

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem canonicalZeroSpatialInputMap_physicalSite
    {X Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    {W : ℝ} (hW : 0 ≤ W) (L τ : ℝ) (N : X → ℕ)
    (z : Option Zsp × X → ℤ) (x : X) :
    canonicalZeroSpatialInputMap s root D W L
      (fun k => (z k : ℝ) / trimmedSpatialWidths W τ N k) ⟨x, Sum.inl ()⟩ =
      (integerPhysicalSite root z x : ℝ) / (τ * (N x : ℝ) / 8) := by
  have hb : (1 + W : ℝ) ≠ 0 := by linarith
  have hn : trimmedSpatialWidths (K := Zsp) W τ N (none, x) = τ * (N x : ℝ) / 8 := by
    simp only [trimmedSpatialWidths, centeredSpatialWidths]
    ring
  have hs (j : Zsp) : trimmedSpatialWidths W τ N (some j, x) =
      (τ * (N x : ℝ) / 8) / (1 + W) := by
    simp only [trimmedSpatialWidths, centeredSpatialWidths, one_mul, div_div]
    ring
  rw [canonicalZeroSpatialInputMap_apply s root D W L hW]
  simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul, hn, hs,
    add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [div_div_eq_mul_div]
  by_cases ht : τ * (N x : ℝ) / 8 = 0
  · simp only [ht, div_zero, mul_zero, zero_div]
  · field_simp

theorem canonicalZeroSpatialNarrowInput_normalized
    {G J X : Type*} {ξ : ℝ} (hξ : ξ ≠ 0) (W τ : ℝ) (N : X → ℕ)
    (z : Option (G ⊕ J) × X → ℤ) :
    canonicalZeroSpatialNarrowInput ξ
      (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ N k) =
      fun k => (z k : ℝ) / trimmedSpatialWidths W τ N k := by
  funext k
  rcases k with ⟨_ | (g | j), x⟩
  · rfl
  · rfl
  · simp only [canonicalZeroSpatialNarrowInput, narrowTrimmedSpatialWidths]
    by_cases hw : trimmedSpatialWidths (K := G ⊕ J) W τ N (some (Sum.inr j), x) = 0
    · simp only [hw, mul_zero, div_zero]
    · field_simp

theorem canonicalZeroSpatialNarrowInputMap_physicalSite
    {G J X : Type*} [Fintype G] [Fintype J] [DecidableEq G] [DecidableEq J]
    (s : Empty ↪ (G ⊕ J)) (root : G ⊕ J → ℤ) (D : Matrix Empty (G ⊕ J) ℤ)
    {W ξ : ℝ} (hW : 0 ≤ W) (hξ : ξ ≠ 0) (L τ : ℝ) (N : X → ℕ)
    (z : Option (G ⊕ J) × X → ℤ) (x : X) :
    canonicalZeroSpatialInputMap s root D W L
      (canonicalZeroSpatialNarrowInput ξ
        (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ N k)) ⟨x, Sum.inl ()⟩ =
      (integerPhysicalSite root z x : ℝ) / (τ * (N x : ℝ) / 8) := by
  rw [canonicalZeroSpatialNarrowInput_normalized hξ W τ N z]
  exact canonicalZeroSpatialInputMap_physicalSite s root D hW L τ N z x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]
variable (s : Empty ↪ G) (sf : Empty ↪ (G ⊕ N))
  (root : G → ℤ) (principal : N → ℤ)
  (D : Matrix Empty G ℤ) (Df : Matrix Empty (G ⊕ N) ℤ) (W L : ℝ)

omit [DecidableEq G] [DecidableEq N] in
theorem canonicalZeroSpatialPrincipal_mass_ratio_le_one (hW : 0 ≤ W)
    (hbudget : (∑ k : G ⊕ N, |((Sum.elim root principal k : ℤ) : ℝ)|) ≤ W) :
    (∑ n, |(principal n : ℝ)|) / (1 + W) ≤ 1 := by
  have hroot0 : 0 ≤ ∑ g, |(root g : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hbudget
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1 + W)).mpr
  linarith

theorem canonicalZeroSpatialNarrow_integral_error
    (hW : 0 ≤ W) (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    {A : ℝ≥0} (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    (hLip : LipschitzWith A φ) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ‖(∫ u, (smoothProductProfile (Option (G ⊕ N) × X) u : ℂ) *
        φ (canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
          (canonicalZeroSpatialNarrowInput ξ u))) -
      ∫ y, φ y ∂canonicalZeroSpatialLaw s root D W L‖ ≤
      (A : ℝ) * (ξ * ((∑ n, |(principal n : ℝ)|) / (1 + W))) := by
  let μ := unitCoefficientSource (Option (G ⊕ N) × X)
  let f := fun u : Option (G ⊕ N) × X → ℝ =>
    φ (canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
      (canonicalZeroSpatialNarrowInput ξ u))
  let g := fun u : Option (G ⊕ N) × X → ℝ =>
    φ (canonicalZeroSpatialInputMap s root D W L
      (u ∘ canonicalZeroSpatialKernelEmbedding G N X))
  have hfmeas : Measurable f := hLip.continuous.measurable.comp
    ((canonicalZeroSpatialInputMap_measurable sf (Sum.elim root principal) Df W L).comp
      (canonicalZeroSpatialNarrowInput_lipschitz ξ hξ0 hξ1).continuous.measurable)
  have hgmeas : Measurable g := hLip.continuous.measurable.comp
    ((canonicalZeroSpatialInputMap_measurable s root D W L).comp
      (unitCoefficientProjection_measurable (canonicalZeroSpatialKernelEmbedding G N X)))
  have hf : Integrable f μ := ⟨hfmeas.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun u => hφ _))⟩
  have hg : Integrable g μ := ⟨hgmeas.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun u => hφ _))⟩
  have hfint : (∫ u, f u ∂μ) = ∫ u,
      (smoothProductProfile (Option (G ⊕ N) × X) u : ℂ) * f u :=
    realDensityMeasure_integral_complex volume _
      (smoothProductProfile_contDiff _).continuous.measurable
      (fun u => (smoothProductProfile_range _ u).1) f
  have hgint : (∫ u, g u ∂μ) = ∫ y, φ y ∂canonicalZeroSpatialLaw s root D W L :=
    canonicalZeroSpatialInputProjection_integral_complex s root D W L
      (canonicalZeroSpatialKernelEmbedding G N X) φ hLip.continuous.measurable
  change ‖(∫ u, (smoothProductProfile (Option (G ⊕ N) × X) u : ℂ) * f u) - _‖ ≤ _
  rw [← hfint, ← hgint, ← integral_sub hf hg]
  have he : ∀ᵐ u ∂μ, ‖f u - g u‖ ≤
      (A : ℝ) * (ξ * ((∑ n, |(principal n : ℝ)|) / (1 + W))) := by
    filter_upwards [unitCoefficientSource_norm_le (Option (G ⊕ N) × X)] with u hu
    exact canonicalZeroSpatialNarrowPrincipal_test_error s sf root principal D Df W L
      hW ξ hξ0 u hu φ hLip
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const he

theorem selectedCanonicalZeroSpatial_narrow_principal_comparison
    (hW : 0 ≤ W)
    (hbudget : (∑ k : G ⊕ N, |((Sum.elim root principal k : ℤ) : ℝ)|) ≤ W)
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (r : ColumnResiduePattern (Option (G ⊕ N)) X modulus)
    (V : Option (G ⊕ N) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r} V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, (modulus z.2 : ℝ) / V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option (G ⊕ N) × X) *
      ((Fintype.card (Option (G ⊕ N) × X) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    {A : ℝ≥0} (hLip : LipschitzWith A φ) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus {r} V hV hZ z).toReal : ℂ) *
        φ (canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
          (canonicalZeroSpatialNarrowInput ξ (fun k => (z k : ℝ) / V k)))) -
      ∫ y, φ y ∂canonicalZeroSpatialLaw s root D W L‖ ≤
      4 * (4 : ℝ) ^ Fintype.card (Option (G ⊕ N) × X) *
        (2 * (A : ℝ) + 2 * ((Fintype.card (Option (G ⊕ N) × X) : ℝ) * probabilityProfileLipschitz)) * δ +
      (A : ℝ) * ξ := by
  let F := fun u : Option (G ⊕ N) × X → ℝ =>
    canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
      (canonicalZeroSpatialNarrowInput ξ u)
  have hF : LipschitzWith 2 F := by
    simpa only [F, Function.comp_def, mul_one] using
      (canonicalZeroSpatialInputMap_lipschitz sf (Sum.elim root principal) Df W L hW hbudget).comp
        (canonicalZeroSpatialNarrowInput_lipschitz ξ hξ0 hξ1)
  have hquad := selectedResidueSmoothPMF_singleton_complex_quadrature modulus hmodulus r V hV hZ
    hδ hδ1 hmesh hsmall (φ ∘ F) (hLip.comp hF) (fun u => hφ _)
  simp only [Function.comp_apply, NNReal.coe_mul, NNReal.coe_ofNat, mul_comm (A : ℝ) 2] at hquad
  have hpert := canonicalZeroSpatialNarrow_integral_error s sf root principal D Df W L
    hW ξ hξ0 hξ1 φ hLip hφ
  have hratio := canonicalZeroSpatialPrincipal_mass_ratio_le_one root principal W hW hbudget
  have he : (A : ℝ) * (ξ * ((∑ n, |(principal n : ℝ)|) / (1 + W))) ≤ (A : ℝ) * ξ := by
    calc
      _ ≤ (A : ℝ) * (ξ * 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hratio hξ0) A.coe_nonneg
      _ = _ := by rw [mul_one]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hquad (hpert.trans he))

theorem selectedNarrowPhysicalSpatial_canonical_comparison
    (hW : 0 ≤ W)
    (hbudget : (∑ k : G ⊕ N, |((Sum.elim root principal k : ℤ) : ℝ)|) ≤ W)
    (τ ξ : ℝ) (hτ : 0 < τ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (r : ColumnResiduePattern (Option (G ⊕ N)) X modulus)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r} (narrowTrimmedSpatialWidths W τ ξ box) z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z : Option (G ⊕ N) × X,
      (modulus z.2 : ℝ) / narrowTrimmedSpatialWidths W τ ξ box z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option (G ⊕ N) × X) *
      ((Fintype.card (Option (G ⊕ N) × X) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    {A : ℝ≥0} (hLip : LipschitzWith A φ) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus {r} (narrowTrimmedSpatialWidths W τ ξ box)
        (narrowTrimmedSpatialWidths_pos hW hτ hξ box hbox) hZ z).toReal : ℂ) *
        φ (fun o : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (Sum.elim root principal) z o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8))) -
      ∫ y, φ y ∂canonicalZeroSpatialLaw s root D W L‖ ≤
      4 * (4 : ℝ) ^ Fintype.card (Option (G ⊕ N) × X) *
        (2 * (A : ℝ) + 2 * ((Fintype.card (Option (G ⊕ N) × X) : ℝ) * probabilityProfileLipschitz)) * δ +
      (A : ℝ) * ξ := by
  let sf : Empty ↪ (G ⊕ N) := ⟨Empty.elim, fun e => Empty.elim e⟩
  let Df : Matrix Empty (G ⊕ N) ℤ := fun e => Empty.elim e
  have he (z : Option (G ⊕ N) × X → ℤ) :
      canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
        (canonicalZeroSpatialNarrowInput ξ
          (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k)) =
      fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (Sum.elim root principal) z o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8) := by
    funext o
    rcases o with ⟨x, a⟩
    cases a with
    | inr e => exact Empty.elim e
    | inl a =>
      cases a
      exact canonicalZeroSpatialNarrowInputMap_physicalSite sf (Sum.elim root principal) Df
        hW hξ.ne' L τ box z x
  have h := selectedCanonicalZeroSpatial_narrow_principal_comparison s sf root principal D Df W L
    hW hbudget ξ hξ.le hξ1 modulus hmodulus r (narrowTrimmedSpatialWidths W τ ξ box)
    (narrowTrimmedSpatialWidths_pos hW hτ hξ box hbox) hZ hδ hδ1 hmesh hsmall φ hLip hφ
  simpa only [he] using h

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

variable (s : Empty ↪ G) (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
variable (τ ξ : ℝ) (box : X → ℕ)

local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box
local notation "root" => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y

theorem allocatedNarrowPhysicalSpatial_canonical_comparison
    (hτ : 0 < τ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hbox : ∀ t, 0 < box t)
    (modulus : X → ℕ) (hmodulus : ∀ t, 0 < modulus t)
    (r : ColumnResiduePattern (Option vars) X modulus)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r} widths z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z : Option vars × X, (modulus z.2 : ℝ) / widths z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option vars × X) *
      ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    {A : ℝ≥0} (hLip : LipschitzWith A φ) (hφ : ∀ z, ‖φ z‖ ≤ 1) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus {r} widths
        (narrowTrimmedSpatialWidths_pos (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
          hτ hξ box hbox) hZ z).toReal : ℂ) *
        φ (fun o : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite root z o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8))) -
      ∫ z, φ z ∂canonicalZeroSpatialLaw s (fun g => (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) budget (S.value : ℝ)‖ ≤
      4 * (4 : ℝ) ^ Fintype.card (Option vars × X) *
        (2 * (A : ℝ) + 2 * ((Fintype.card (Option vars × X) : ℝ) * probabilityProfileLipschitz)) * δ +
      (A : ℝ) * ξ := by
  classical
  have hr : root = Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) := by
    funext k
    simp only [allocatedPhysicalCubeRoot, zero_add]
  have hbudget : (∑ k : vars,
      |((Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k : ℤ) : ℝ)|) ≤ budget := by
    simpa only [hr] using allocatedPhysicalCube_root_sum B U basis S (fun _ => 0) x y
  have he := selectedNarrowPhysicalSpatial_canonical_comparison s
    (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ))
    (scalarCubeDifferenceMatrix x) budget (S.value : ℝ)
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hbudget
    τ ξ hτ hξ hξ1 box hbox modulus hmodulus r hZ hδ hδ1 hmesh hsmall φ hLip hφ
  simpa only [hr] using he

end Erdos3.VectorPolynomial

end

end OAI
