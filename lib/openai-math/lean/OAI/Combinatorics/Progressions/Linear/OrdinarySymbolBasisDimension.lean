import OAI.Combinatorics.Progressions.Dynamics.PointwiseSymbolBudget
import OAI.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem homogeneousSymbolLift_mem_pointwise (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule)
    (α : σ →₀ ℕ) (v : F.AssociatedGraded) (hv : v ∈ U) :
    F.homogeneousSymbolLift b ω hlayers w α v ∈ F.symbolPointwiseSubalgebra b ω hlayers w U := by
  classical
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  intro β
  rw [F.gradedSymbolPolynomial_homogeneousSymbolLift, coefficients_monomial]
  by_cases h : α = β
  · subst β
    rw [Finsupp.single_eq_same]
    exact hU (Finsupp.weight w α) v hv
  · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
    exact U.zero_mem

noncomputable def pointwiseSymbolSpanningFamily (v : κ → F.AssociatedGraded) :
    SymbolBasisIndex w ω × κ → F.PolynomialSymbol w :=
  fun z => F.homogeneousSymbolLift b ω hlayers w z.1.val.1 (v z.2)

theorem pointwiseSymbolSpanningFamily_span [Fintype (SymbolBasisIndex w ω)]
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v)) =
      (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply F.homogeneousSymbolLift_mem_pointwise b ω hlayers w U hU
    change v z.2 ∈ U.toSubmodule
    rw [← hspan]
    exact Submodule.subset_span ⟨z.2, rfl⟩
  · intro x hx
    rw [← sum_basisBlockProjection (F.polynomialSymbolBasis b ω hlayers w) (fun z => z.val.1) x]
    apply Submodule.sum_mem
    intro α hα
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hα
    rw [← F.homogeneousSymbolLift_coefficient]
    let W := Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v))
    have hmap : U.toSubmodule ≤ W.comap (F.homogeneousSymbolLift b ω hlayers w z.val.1) := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(z, j), rfl⟩
    exact hmap ((F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U x).mp hx z.val.1)

theorem pointwiseSymbolSpanningFamily_height (v : κ → F.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j) i) H) :
    ∀ z i, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
      (F.pointwiseSymbolSpanningFamily b ω hlayers w v z) i) H := by
  classical
  intro z i
  change RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
    (F.homogeneousSymbolLift b ω hlayers w z.1.val.1 (v z.2)) i) H
  rw [F.homogeneousSymbolLift_coordinate]
  split_ifs
  · exact hv z.2 i.val.2
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def pointwiseFastSectionInput (s : ℕ) (p : ℝ) : ℝ :=
  2 * (p + (s + 3)) ^ (s + 3) + ((p + (s + 3)) ^ (s + 3)) ^ 2 + p

theorem pointwiseFastSectionInput_ge (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ pointwiseFastSectionInput s p := by
  unfold pointwiseFastSectionInput
  exact le_add_of_nonneg_left (by positivity)

theorem symbolBasisIndex_card_le_spanning_budget
    {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) [Fintype (SymbolBasisIndex w ω)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ (p + (s + 3)) ^ (s + 3) := by
  apply (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
    (F.adaptedBasis_weight_le_step b ω hF))).trans
  apply (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ).trans
  apply (pow_le_pow_left₀ (by positivity : 0 ≤ p + (s + 2))
    (by linarith : p + (s + 2 : ℝ) ≤ p + (s + 3)) (s + 2)).trans
  exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) s; linarith) (by omega)

theorem pointwiseSymbolSpanning_section_counts
    {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype ξ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w τ)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hξ : (Fintype.card ξ : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex w ω × ξ) : ℝ) ≤ pointwiseFastSectionInput s p ∧
    (Fintype.card (SymbolBasisIndex w ω ⊕ SymbolBasisIndex w τ) : ℝ) ≤
      pointwiseFastSectionInput s p ∧
    ((Fintype.card (SymbolBasisIndex w ω) *
      Fintype.card (SymbolBasisIndex w ω × ξ) : ℕ) : ℝ) ≤ pointwiseFastSectionInput s p := by
  let A : ℝ := (p + (s + 3)) ^ (s + 3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb := F.symbolBasisIndex_card_le_spanning_budget b ω hF w hw hp hι hσ
  have hc := G.symbolBasisIndex_card_le_spanning_budget c τ hG w hw hp hκ hσ
  have hv : (Fintype.card (SymbolBasisIndex w ω × ξ) : ℝ) ≤ A := by
    have hnat : Fintype.card (SymbolBasisIndex w ω × ξ) ≤
        Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s * Fintype.card ξ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ω s hw
        (F.adaptedBasis_weight_le_step b ω hF))
    exact (Nat.cast_le.mpr hnat).trans (symbol_spanning_count_bound s _ _ _ hp hι hσ hξ)
  have hrows : (Fintype.card (SymbolBasisIndex w ω ⊕ SymbolBasisIndex w τ) : ℝ) ≤ 2 * A := by
    rw [Fintype.card_sum, Nat.cast_add]
    dsimp only [A]
    linarith
  have hcols : ((Fintype.card (SymbolBasisIndex w ω) *
      Fintype.card (SymbolBasisIndex w ω × ξ) : ℕ) : ℝ) ≤ A ^ 2 := by
    rw [Nat.cast_mul, pow_two]
    exact mul_le_mul hb hv (Nat.cast_nonneg _) hA
  change _ ≤ 2 * A + A ^ 2 + p ∧ _ ≤ 2 * A + A ^ 2 + p ∧ _ ≤ 2 * A + A ^ 2 + p
  refine ⟨hv.trans ?_, hrows.trans ?_, hcols.trans ?_⟩ <;> nlinarith [sq_nonneg A]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

@[instance_reducible] noncomputable def ordinarySymbolBasisFintype :
    Fintype (SymbolBasisIndex (fun _ : σ => 1) ω) :=
  symbolBasisIndexFintype (fun _ : σ => 1) ω s (fun _ => Nat.zero_lt_one)
    (F.adaptedBasis_weight_le_step b ω hF)

include hF

theorem ordinarySymbolBasisIndex_card_le
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    {p : ℝ} (hp : 0 ≤ p)
    (hdimension : (Fintype.card ι : ℝ) + (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤
      (p + (s + 3)) ^ (s + 3) := by
  apply F.symbolBasisIndex_card_le_spanning_budget b ω hF (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) hp
  · exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hdimension
  · exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hdimension

theorem ordinarySymbolBasisFintype_card_le
    {p : ℝ} (hp : 0 ≤ p)
    (hdimension : (Fintype.card ι : ℝ) + (Fintype.card σ : ℝ) ≤ p) :
    (@Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω)
      (F.ordinarySymbolBasisFintype b ω hF) : ℝ) ≤
      (p + (s + 3)) ^ (s + 3) := by
  let : Fintype (SymbolBasisIndex (fun _ : σ => 1) ω) :=
    F.ordinarySymbolBasisFintype b ω hF
  exact F.ordinarySymbolBasisIndex_card_le b ω hF hp hdimension

theorem ordinaryPolynomialSymbol_finrank_le
    {p : ℝ} (hp : 0 ≤ p)
    (hdimension : (Fintype.card ι : ℝ) + (Fintype.card σ : ℝ) ≤ p) :
    (finrank ℚ (F.PolynomialSymbol (fun _ : σ => 1)) : ℝ) ≤
      (p + (s + 3)) ^ (s + 3) := by
  let : Fintype (SymbolBasisIndex (fun _ : σ => 1) ω) :=
    F.ordinarySymbolBasisFintype b ω hF
  rw [finrank_eq_card_basis (F.polynomialSymbolBasis b ω hF (fun _ : σ => 1))]
  exact F.ordinarySymbolBasisIndex_card_le b ω hF hp hdimension

omit hF in

theorem pointwiseFastSectionInput_le_envelope (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    pointwiseFastSectionInput s p ≤ (p + (s + 5)) ^ (2 * (s + 4)) := by
  let A : ℝ := (p + (s + 3)) ^ (s + 3)
  let B : ℝ := (p + (s + 5)) ^ (s + 3)
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hx : 1 ≤ p + (s + 3 : ℝ) := by linarith
  have hy : 2 ≤ p + (s + 5 : ℝ) := by linarith
  have hA : 1 ≤ A := one_le_pow₀ hx
  have hpA : p ≤ A := by
    calc
      p ≤ p + (s + 3 : ℝ) := by linarith
      _ = (p + (s + 3 : ℝ)) ^ 1 := by simp
      _ ≤ A := pow_le_pow_right₀ hx (by omega)
  have hAB : A ≤ B := pow_le_pow_left₀ (by positivity)
    (by linarith : p + (s + 3 : ℝ) ≤ p + (s + 5 : ℝ)) _
  have hABsq : A ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (by positivity) hAB 2
  have hy2 : 4 ≤ (p + (s + 5 : ℝ)) ^ 2 := by nlinarith
  change 2 * A + A ^ 2 + p ≤ _
  calc
    2 * A + A ^ 2 + p ≤ 4 * A ^ 2 := by nlinarith [sq_nonneg (A - 1)]
    _ ≤ (p + (s + 5 : ℝ)) ^ 2 * B ^ 2 :=
      mul_le_mul hy2 hABsq (sq_nonneg _) (sq_nonneg _)
    _ = (p + (s + 5)) ^ (2 * (s + 4)) := by
      dsimp [B]
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

end Erdos3.NilpotentLieFiltration

end

end OAI
