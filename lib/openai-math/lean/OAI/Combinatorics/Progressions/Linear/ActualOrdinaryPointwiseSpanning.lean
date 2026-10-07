import OAI.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection
import OAI.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem associatedGradedMap_basis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hφH : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p) (i : ι) (j : κ) :
    rationalLogHeight ((G.associatedGradedBasis f ν hG).repr
      (F.associatedGradedMap G φ hφ (F.associatedGradedBasis e ω hF i)) j) ≤ p := by
  classical
  rw [F.associatedGradedMap_basis_repr G e ω hF f ν hG φ hφ]
  split_ifs
  · exact hφH i j
  · simpa [rationalLogHeight] using hp

theorem exists_associatedGradedMap_comap_bounded_spanning [Fintype ι] [Fintype κ]
    (U : LieSubalgebra ℚ G.AssociatedGraded) (v : κ → G.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ a j, rationalLogHeight ((G.associatedGradedBasis f ν hG).repr (v a) j) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p) :
    ∃ u : ι → F.AssociatedGraded,
      Submodule.span ℚ (Set.range u) =
        (U.comap (F.associatedGradedMap G φ hφ)).toSubmodule ∧
      ∀ a i, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (u a) i) ≤
        preimageBasisBudget p + 1 := by
  classical
  let eA := F.associatedGradedBasis e ω hF
  let fA := G.associatedGradedBasis f ν hG
  let T := (F.associatedGradedMap G φ hφ).toLinearMap
  let K := U.toSubmodule.comap T
  have heH (a i : ι) : rationalLogHeight (eA.repr (eA a) i) ≤ p := by
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simpa [rationalLogHeight] using hp
  obtain ⟨b, hb⟩ := exists_preimage_basis_logHeight eA fA ⊤ U.toSubmodule T eA v
    eA.span_eq hv hp hκ hι hκ heH hvH
    (F.associatedGradedMap_basis_logHeight G e ω hF f ν hG φ hφ hp hφH)
  have hspan : Submodule.span ℚ (Set.range (fun a => (b a : F.AssociatedGraded))) = K := by
    change Submodule.span ℚ (Set.range ((⊤ ⊓ K).subtype ∘ b)) = K
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype, top_inf_eq]
  obtain ⟨z, hz, hzH⟩ := exists_bounded_submodule_ambient_spanning eA K
    (fun a => (b a : F.AssociatedGraded)) hspan (one_le_ceil_exp (preimageBasisBudget p))
    (fun a i => rationalHeightLE_ceil_exp (hb a i))
  refine ⟨fun a => z (Fintype.equivFin ι a), ?_, fun a i => ?_⟩
  · change Submodule.span ℚ (Set.range (z ∘ Fintype.equivFin ι)) = K
    rw [Set.range_comp, (Fintype.equivFin ι).surjective.range_eq, Set.image_univ]
    exact hz
  · exact rationalLogHeight_le_of_height (hzH _ i)
      (ceil_exp_le_exp_add_one (preimageBasisBudget_nonneg hp))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ γ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def gradedImageSpanningFamily (v : γ → F.AssociatedGraded) :
    γ → G.AssociatedGraded := fun a => F.associatedGradedMap G φ hφ (v a)

theorem gradedImageSpanningFamily_span (W : LieSubalgebra ℚ F.AssociatedGraded)
    (v : γ → F.AssociatedGraded) (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (F.gradedImageSpanningFamily G φ hφ v)) =
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule := by
  change Submodule.span ℚ (Set.range ((F.associatedGradedMap G φ hφ).toLinearMap ∘ v)) =
    W.toSubmodule.map (F.associatedGradedMap G φ hφ).toLinearMap
  rw [Set.range_comp, ← Submodule.map_span, hv]

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem gradedImageSpanningFamily_logHeight [Fintype ι]
    (v : γ → F.AssociatedGraded) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) (a : γ) (j : κ) :
    rationalLogHeight ((G.associatedGradedBasis c ν hG).repr
      (F.gradedImageSpanningFamily G φ hφ v a) j) ≤ (p + 2) ^ 4 := by
  exact linearMap_coordinate_logHeight (F.associatedGradedBasis e ω hF)
    (G.associatedGradedBasis c ν hG) (F.associatedGradedMap G φ hφ).toLinearMap hp hι
    (F.associatedGradedMap_basis_logHeight G e ω hF c ν hG φ hφ hp hφH) (v a) (hvH a) j

theorem gradedImage_bounded_spanning [Fintype ι]
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) :
    Submodule.span ℚ (Set.range (F.gradedImageSpanningFamily G φ hφ v)) =
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    BasisGradedSubmodule (G.associatedGradedBasis c ν hG) ν
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    ∀ a j, rationalLogHeight ((G.associatedGradedBasis c ν hG).repr
      (F.gradedImageSpanningFamily G φ hφ v a) j) ≤ (p + 2) ^ 4 := by
  exact ⟨F.gradedImageSpanningFamily_span G φ hφ W v hv,
    F.associatedGradedMap_image_graded G e ω hF c ν hG φ hφ W hW,
    F.gradedImageSpanningFamily_logHeight G φ hφ e ω hF c ν hG v hp hι hvH hφH⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem gradedImagePointwiseSpanning_heightBound {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4)).trans
  apply Real.exp_le_exp.mpr
  have hpow : 1 ≤ (p + 2) ^ 4 := one_le_pow₀ (by linarith)
  calc
    (p + 2) ^ 4 + 1 ≤ (p + 2) ^ 4 + (p + 2) ^ 4 := by linarith only [hpow]
    _ = (p + 2) ^ 4 * 2 := by ring
    _ ≤ (p + 2) ^ 4 * (p + 2) :=
      mul_le_mul_of_nonneg_left (by linarith : 2 ≤ p + 2) (by positivity)
    _ = (p + 2) ^ 5 := by ring

theorem pointwiseSpanningIndex_card_le
    {σ κ γ M : Type*} [Fintype σ] [Fintype κ] [Fintype γ]
    [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
    (G : NilpotentLieFiltration M t) (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) [Fintype (SymbolBasisIndex w ν)]
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex w ν × γ) : ℝ) ≤ pointwiseFastSectionInput t p :=
  (G.pointwiseSymbolSpanning_section_counts (ξ := γ) G c ν hG c ν hG w hw
    hp hκ hκ hγ hσ).1

variable {σ ι κ γ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (w : σ → ℕ)

noncomputable def gradedImagePointwiseSpanningFamily (v : γ → F.AssociatedGraded) :
    SymbolBasisIndex w ν × γ → G.PolynomialSymbol w :=
  G.pointwiseSymbolSpanningFamily c ν hG w (F.gradedImageSpanningFamily G φ hφ v)

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedImagePointwiseSpanningFamily_span [Fintype (SymbolBasisIndex w ν)]
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v)) =
      (G.symbolPointwiseSubalgebra c ν hG w
        (W.map (F.associatedGradedMap G φ hφ))).toSubmodule := by
  exact G.pointwiseSymbolSpanningFamily_span c ν hG w
    (W.map (F.associatedGradedMap G φ hφ))
    (F.associatedGradedMap_image_graded G e ω hF c ν hG φ hφ W hW)
    (F.gradedImageSpanningFamily G φ hφ v)
    (F.gradedImageSpanningFamily_span G φ hφ W v hv)

theorem gradedImagePointwiseSpanningFamily_height [Fintype ι]
    (v : γ → F.AssociatedGraded) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight
      ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) :
    ∀ z i, RationalHeightLE ((G.polynomialSymbolBasis c ν hG w).repr
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v z) i)
        ⌈Real.exp ((p + 2) ^ 4)⌉₊ := by
  exact G.pointwiseSymbolSpanningFamily_height c ν hG w
    (F.gradedImageSpanningFamily G φ hφ v) (one_le_ceil_exp _)
    (fun a j => rationalHeightLE_ceil_exp
      (F.gradedImageSpanningFamily_logHeight G φ hφ e ω hF c ν hG v hp hι hvH hφH a j))

theorem gradedImagePointwiseSpanningFamily_controlled
    [Fintype σ] [Fintype ι] [Fintype κ] [Fintype γ]
    [Fintype (SymbolBasisIndex w ν)]
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hw : ∀ i, 0 < w i) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight
      ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) :
    Submodule.span ℚ (Set.range
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v)) =
        (G.symbolPointwiseSubalgebra c ν hG w
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule ∧
    BasisGradedSubmodule (G.associatedGradedBasis c ν hG) ν
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    (∀ z i, RationalHeightLE ((G.polynomialSymbolBasis c ν hG w).repr
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v z) i)
        ⌈Real.exp ((p + 2) ^ 4)⌉₊) ∧
    (Fintype.card (SymbolBasisIndex w ν × γ) : ℝ) ≤ pointwiseFastSectionInput t p ∧
    1 ≤ ⌈Real.exp ((p + 2) ^ 4)⌉₊ ∧
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  exact ⟨F.gradedImagePointwiseSpanningFamily_span G φ hφ c ν hG w e ω hF W v hW hv,
    F.associatedGradedMap_image_graded G e ω hF c ν hG φ hφ W hW,
    F.gradedImagePointwiseSpanningFamily_height G φ hφ c ν hG w e ω hF v hp hι hvH hφH,
    G.pointwiseSpanningIndex_card_le c ν hG w hw hp hκ hγ hσ,
    one_le_ceil_exp _, gradedImagePointwiseSpanning_heightBound hp⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

noncomputable def ordinaryImagePointwiseBudget (s t : ℕ) (p : ℝ) : ℝ :=
  pointwiseFastSectionInput s p + pointwiseFastSectionInput t p + (p + 2) ^ 5

private theorem sectionInput_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ pointwiseFastSectionInput s p := by
  unfold pointwiseFastSectionInput
  positivity

theorem ordinaryImagePointwiseBudget_source (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    pointwiseFastSectionInput s p ≤ ordinaryImagePointwiseBudget s t p := by
  have ht := sectionInput_nonneg t hp
  have hh : 0 ≤ (p + 2) ^ 5 := by positivity
  unfold ordinaryImagePointwiseBudget
  linarith

theorem ordinaryImagePointwiseBudget_target (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    pointwiseFastSectionInput t p ≤ ordinaryImagePointwiseBudget s t p := by
  have hs := sectionInput_nonneg s hp
  have hh : 0 ≤ (p + 2) ^ 5 := by positivity
  unfold ordinaryImagePointwiseBudget
  linarith

theorem ordinaryImagePointwiseBudget_height (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + 2) ^ 5 ≤ ordinaryImagePointwiseBudget s t p := by
  have hs := sectionInput_nonneg s hp
  have ht := sectionInput_nonneg t hp
  unfold ordinaryImagePointwiseBudget
  linarith

theorem ordinaryImagePointwiseBudget_ge (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ ordinaryImagePointwiseBudget s t p :=
  (pointwiseFastSectionInput_ge s hp).trans (ordinaryImagePointwiseBudget_source s t hp)

private theorem symbolCount_le_sectionInput (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + (s + 3)) ^ (s + 3) ≤ pointwiseFastSectionInput s p := by
  have h : 0 ≤ (p + (s + 3)) ^ (s + 3) := by positivity
  unfold pointwiseFastSectionInput
  nlinarith [sq_nonneg ((p + (s + 3)) ^ (s + 3))]

variable {σ ι κ γ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype γ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem ordinaryGradedImagePointwiseSpanning_controlled
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight
      ((F.associatedGradedBasis b ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p) :
    let vg := F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG (fun _ : σ => 1) v
    Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule ∧
    BasisGradedSubmodule (G.associatedGradedBasis c ν hG) ν
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    (∀ z i, RationalHeightLE ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr
      (vg z) i) ⌈Real.exp ((p + 2) ^ 4)⌉₊) ∧
    (Nat.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ ordinaryImagePointwiseBudget s t p ∧
    (Nat.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ ordinaryImagePointwiseBudget s t p ∧
    (Nat.card (SymbolBasisIndex (fun _ : σ => 1) ν × γ) : ℝ) ≤ ordinaryImagePointwiseBudget s t p ∧
    1 ≤ ⌈Real.exp ((p + 2) ^ 4)⌉₊ ∧
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp (ordinaryImagePointwiseBudget s t p) := by
  let : Fintype (SymbolBasisIndex (fun _ : σ => 1) ω) :=
    F.ordinarySymbolBasisFintype b ω hF
  let : Fintype (SymbolBasisIndex (fun _ : σ => 1) ν) :=
    G.ordinarySymbolBasisFintype c ν hG
  obtain ⟨hspan, hgraded, hheight, hcount, hH, hHexp⟩ :=
    F.gradedImagePointwiseSpanningFamily_controlled G φ hφ c ν hG (fun _ : σ => 1)
      b ω hF W v hW hv (fun _ => Nat.zero_lt_one) hp hι hκ hγ hσ hvH hφH
  refine ⟨hspan, hgraded, hheight, ?_, ?_, ?_, hH, ?_⟩
  · have hsource := F.symbolBasisIndex_card_le_spanning_budget b ω hF
      (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) hp hι hσ
    simpa only [Nat.card_eq_fintype_card] using
      (hsource.trans (symbolCount_le_sectionInput s hp)).trans
        (ordinaryImagePointwiseBudget_source s t hp)
  · have htarget := G.symbolBasisIndex_card_le_spanning_budget c ν hG
      (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) hp hκ hσ
    simpa only [Nat.card_eq_fintype_card] using
      (htarget.trans (symbolCount_le_sectionInput t hp)).trans
        (ordinaryImagePointwiseBudget_target s t hp)
  · simpa only [Nat.card_eq_fintype_card] using
      hcount.trans (ordinaryImagePointwiseBudget_target s t hp)
  · exact hHexp.trans (Real.exp_le_exp.mpr (ordinaryImagePointwiseBudget_height s t hp))

end Erdos3.NilpotentLieFiltration

end

end OAI
