import OAI.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
import OAI.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
import OAI.Combinatorics.Progressions.Lattices.FullAffineCoefficientBound
import OAI.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
import OAI.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
import OAI.Combinatorics.Progressions.Sampling.RealAdaptedCoefficientGrid

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

def CoefficientBound (b : Basis ι ℝ L) (T : σ → ℝ) (M : ℝ)
    (P : VectorPolynomial σ ℚ L) : Prop :=
  ∀ α i, |b.repr (coefficients P α) i| ≤ M / monomialScale T α

def CoefficientGrid (b : Basis ι ℝ L) (l : ℕ) (P : VectorPolynomial σ ℚ L) : Prop :=
  ∀ α, (fun i => b.repr (coefficients P α) i) ∈ realDenominatorGrid l

theorem coefficientBound_iff_norm [Fintype ι] (b : Basis ι ℝ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ L) :
    CoefficientBound b T M P ↔ ∀ α, ‖b.equivFun (coefficients P α)‖ ≤ M / monomialScale T α := by
  constructor
  · intro h α
    exact (pi_norm_le_iff_of_nonneg (div_nonneg hM (monomialScale_pos T hT α).le)).mpr (h α)
  · intro h α i
    exact (norm_le_pi_norm (b.equivFun (coefficients P α)) i).trans (h α)

theorem CoefficientBound.mono (b : Basis ι ℝ L) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} {P : VectorPolynomial σ ℚ L} (h : CoefficientBound b T M P) (hMN : M ≤ N) :
    CoefficientBound b T N P := by
  intro α i
  exact (h α i).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT α).le)

theorem CoefficientBound.neg (b : Basis ι ℝ L) (T : σ → ℝ) {M : ℝ}
    {P : VectorPolynomial σ ℚ L} (h : CoefficientBound b T M P) : CoefficientBound b T M (-P) := by
  intro α i
  simpa only [map_neg, Finsupp.neg_apply, abs_neg] using h α i

theorem CoefficientBound.sub (b : Basis ι ℝ L) (T : σ → ℝ) {M N : ℝ}
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientBound b T M P) (hQ : CoefficientBound b T N Q) :
    CoefficientBound b T (M + N) (P - Q) := by
  intro α i
  simp only [map_sub, Finsupp.sub_apply]
  exact (abs_sub _ _).trans ((add_le_add (hP α i) (hQ α i)).trans_eq (by ring))

theorem CoefficientGrid.sub (b : Basis ι ℝ L) (l : ℕ)
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientGrid b l P) (hQ : CoefficientGrid b l Q) :
    CoefficientGrid b l (P - Q) := by
  intro α
  simp only [map_sub, Finsupp.sub_apply]
  exact realDenominatorGrid_sub l _ _ (hP α) (hQ α)

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF in
theorem gradedPolynomial_mem_adapted (w : σ → ℕ) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω w) :
    P ∈ F.realification.adaptedLieSubalgebra w := by
  intro α
  have h := F.realGradeProjection_mem_layer b ω hF (Finsupp.weight w α) (coefficients P α)
  have he : basisGradeProjection (b.baseChange ℝ) ω (Finsupp.weight w α) (coefficients P α) = coefficients P α := hP α
  rw [he] at h
  exact h

include hF in
theorem shiftedGradedPolynomial_mem_adapted (w : σ → ℕ) (r : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω w r) :
    P ∈ F.realification.adaptedLieSubalgebra w := by
  intro α
  have h := F.realGradeProjection_mem_layer b ω hF (Finsupp.weight w α + r) (coefficients P α)
  have he : basisGradeProjection (b.baseChange ℝ) ω (Finsupp.weight w α + r) (coefficients P α) = coefficients P α := hP α
  rw [he] at h
  exact F.realification.antitone (Nat.le_add_right _ _) h

include b ω hF in
theorem exists_real_adapted_representation (w : σ → ℕ) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ F.realification.adaptedLieSubalgebra w) :
    ∃ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w, F.realAdaptedPolynomialMap w x = P := by
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF ⟨P, hP⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem realAdaptedCoefficientBound_iff_formal (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientBound b ω hF w T M x ↔
      CoefficientBound (b.baseChange ℝ) T M (F.realAdaptedPolynomialMap w x) :=
  F.realAdaptedCoefficientBound_polynomial_iff b ω hF w T hT hM ⟨x⟩

theorem realAdaptedCoefficientGrid_iff_formal (w : σ → ℕ) (l : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientGrid b ω hF w l x ↔
      CoefficientGrid (b.baseChange ℝ) l (F.realAdaptedPolynomialMap w x) := by
  rw [F.realAdaptedCoefficientGrid_polynomial_iff b ω hF w l ⟨x⟩]
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext (fun i => congrFun ha (α, i))⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

noncomputable def adaptedFullPolynomialHom (F : NilpotentLieFiltration L s) (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* PolynomialGroup σ F.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.adaptedLieSubalgebra w).incl

@[simp] theorem adaptedFullPolynomialHom_coord (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.adaptedFullPolynomialHom w g).coord = (g.coord : VectorPolynomial σ ℚ L) := rfl

theorem exists_adapted_polynomial_list_lift (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (rs : List (PolynomialGroup σ F.lowerCentralSeries_eq_bot))
    (hadapted : ∀ r ∈ rs, r.coord ∈ F.adaptedLieSubalgebra w) :
    ∃ xs : List (F.adaptedPolynomialFiltration w).Group,
      xs.map (F.adaptedFullPolynomialHom w) = rs := by
  induction rs with
  | nil => exact ⟨[], rfl⟩
  | cons r rs ih =>
    obtain ⟨xs, hxs⟩ := ih (fun x hx => hadapted x (List.mem_cons_of_mem r hx))
    let x : (F.adaptedPolynomialFiltration w).Group := ⟨⟨r.coord, hadapted r (List.mem_cons_self)⟩⟩
    have hx : F.adaptedFullPolynomialHom w x = r := NilpotentLieBCHGroup.ext rfl
    exact ⟨x :: xs, by rw [List.map_cons, hx, hxs]⟩

theorem polynomialRationalGrid_iff_formal {ι : Type*} (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (w : σ → ℕ) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialRationalGrid b w l g ↔
      CoefficientGrid (b.baseChange ℝ) l (F.realification.adaptedFullPolynomialHom w g).coord := by
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext (fun i => congrFun ha (α, i))⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

theorem polynomialSlowBound_iff_formal {ι : Type*} (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialSlowBound b w T M g ↔
      CoefficientBound (b.baseChange ℝ) T M (F.realification.adaptedFullPolynomialHom w g).coord :=
  Iff.rfl

theorem exists_formal_polynomial_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot), rs.length ≤ k →
      (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
      (∀ r ∈ rs, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) r.coord) →
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) rs.prod.coord := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_slow_product_bound s a k
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure T hT rs hlen hadapted hbound
  obtain ⟨xs, hxs⟩ := F.realification.exists_adapted_polynomial_list_lift (fun _ => 1) rs hadapted
  have hxlen : xs.length ≤ k := by simpa only [← hxs, List.length_map] using hlen
  have hxbound : ∀ x ∈ xs, F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) x := by
    intro x hx
    have hmem : F.realification.adaptedFullPolynomialHom (fun _ => 1) x ∈ rs := by
      rw [← hxs]
      exact List.mem_map_of_mem hx
    exact (F.polynomialSlowBound_iff_formal b _ T _ x).mpr (hbound _ hmem)
  have hout := (F.polynomialSlowBound_iff_formal b _ T _ xs.prod).mp (
    hprod F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) H p hH hp hι hσ hHp hstructure
      T hT xs hxlen hxbound)
  rwa [map_list_prod, hxs] at hout

theorem exists_formal_polynomial_product_grid (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot), rs.length ≤ k →
        (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ r ∈ rs, CoefficientGrid (b.baseChange ℝ) l r.coord) →
        CoefficientGrid (b.baseChange ℝ) m rs.prod.coord := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_rational_product_bound s k
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    hprod F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro rs hlen hadapted hbound
  obtain ⟨xs, hxs⟩ := F.realification.exists_adapted_polynomial_list_lift (fun _ => 1) rs hadapted
  have hxlen : xs.length ≤ k := by simpa only [← hxs, List.length_map] using hlen
  have hxgrid : ∀ x ∈ xs, F.PolynomialRationalGrid b (fun _ => 1) l x := by
    intro x hx
    have hmem : F.realification.adaptedFullPolynomialHom (fun _ => 1) x ∈ rs := by
      rw [← hxs]
      exact List.mem_map_of_mem hx
    exact (F.polynomialRationalGrid_iff_formal b _ l x).mpr (hbound _ hmem)
  have hout := (F.polynomialRationalGrid_iff_formal b _ m xs.prod).mp (hgrid xs hxlen hxgrid)
  rwa [map_list_prod, hxs] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

section Modules

variable {σ ι κ L M : Type*} [AddCommGroup L] [Module ℚ L]
  [AddCommGroup M] [Module ℚ M]

noncomputable def sectionCorrectedPolynomial (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  p - VectorPolynomial.map ((S.baseChange ℝ).restrictScalars ℚ)
    (VectorPolynomial.map ((φ.baseChange ℝ).restrictScalars ℚ) p - q)

@[simp] theorem sectionCorrectedPolynomial_coefficients (φ : L →ₗ[ℚ] M)
    (S : M →ₗ[ℚ] L) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) (α : σ →₀ ℕ) :
    coefficients (sectionCorrectedPolynomial φ S p q) α =
      coefficients p α - S.baseChange ℝ
        (φ.baseChange ℝ (coefficients p α) - coefficients q α) := by
  simp only [sectionCorrectedPolynomial, map_sub, Finsupp.sub_apply, coefficients_map,
    LinearMap.restrictScalars_apply]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sectionCorrectedPolynomial_coefficient_norm
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K : ℕ} (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) (T : σ → ℝ) (A B : ℝ)
    (α : σ →₀ ℕ)
    (hp : ‖(b.baseChange ℝ).equivFun (coefficients p α)‖ ≤ A / monomialScale T α)
    (hq : ‖(c.baseChange ℝ).equivFun (coefficients q α)‖ ≤ B / monomialScale T α) :
    ‖(b.baseChange ℝ).equivFun (coefficients (sectionCorrectedPolynomial φ S p q) α)‖ ≤
      (A + (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
        ((((Fintype.card ι : ℝ) + 1) * (H + 1)) * A + B)) / monomialScale T α := by
  rw [sectionCorrectedPolynomial_coefficients]
  apply (realified_section_correction_coordinate_norm b c φ S hφ hS
    (coefficients p α) (coefficients q α)).trans
  calc
    _ ≤ A / monomialScale T α + (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
        (((Fintype.card ι : ℝ) + 1) * (H + 1) * (A / monomialScale T α) +
          B / monomialScale T α) := by
      exact add_le_add hp (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hp (by positivity)) hq) (by positivity))
    _ = _ := by ring

theorem sectionCorrectedPolynomial_denominator_bounds
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K l : ℕ} (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K) (hl : 0 < l) :
    0 < matrixDenominator (LinearMap.toMatrix c b S) *
      matrixDenominator (LinearMap.toMatrix b c φ) * l ∧
    l ∣ matrixDenominator (LinearMap.toMatrix c b S) *
      matrixDenominator (LinearMap.toMatrix b c φ) * l ∧
    matrixDenominator (LinearMap.toMatrix c b S) *
      matrixDenominator (LinearMap.toMatrix b c φ) * l ≤
      K ^ (Fintype.card ι * Fintype.card κ) *
        H ^ (Fintype.card κ * Fintype.card ι) * l := by
  exact ⟨Nat.mul_pos (Nat.mul_pos (matrixDenominator_pos _) (matrixDenominator_pos _)) hl,
    dvd_mul_left _ _,
    Nat.mul_le_mul_right l (Nat.mul_le_mul (matrixDenominator_le _ hS)
      (matrixDenominator_le _ hφ))⟩

theorem sectionCorrectedPolynomial_coefficient_grid
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) {l : ℕ} (hl : 0 < l) (α : σ →₀ ℕ)
    (hp : (b.baseChange ℝ).equivFun (coefficients p α) ∈ realDenominatorGrid l)
    (hq : (c.baseChange ℝ).equivFun (coefficients q α) ∈ realDenominatorGrid l) :
    (b.baseChange ℝ).equivFun (coefficients (sectionCorrectedPolynomial φ S p q) α) ∈
      realDenominatorGrid (matrixDenominator (LinearMap.toMatrix c b S) *
        matrixDenominator (LinearMap.toMatrix b c φ) * l) := by
  let D := matrixDenominator (LinearMap.toMatrix b c φ)
  let E := matrixDenominator (LinearMap.toMatrix c b S)
  have hinner : (c.baseChange ℝ).equivFun
      (φ.baseChange ℝ (coefficients p α) - coefficients q α) ∈
      realDenominatorGrid (D * l) := by
    rw [map_sub]
    exact realDenominatorGrid_sub (D * l) _ _
      (realified_linear_coordinate_grid b c φ l _ hp)
      (realDenominatorGrid_subset_of_dvd hl (dvd_mul_left l D) hq)
  have hcorr : (b.baseChange ℝ).equivFun
      (S.baseChange ℝ (φ.baseChange ℝ (coefficients p α) - coefficients q α)) ∈
      realDenominatorGrid (E * D * l) := by
    simpa only [mul_assoc] using realified_linear_coordinate_grid c b S (D * l) _ hinner
  rw [sectionCorrectedPolynomial_coefficients, map_sub]
  exact realDenominatorGrid_sub (E * D * l) _ _
    (realDenominatorGrid_subset_of_dvd hl (dvd_mul_left l (E * D)) hp) hcorr

end Modules

section LieModules

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sectionCorrectedPolynomial_coefficientBound
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K : ℕ} (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : CoefficientBound (b.baseChange ℝ) T A p)
    (hq : CoefficientBound (c.baseChange ℝ) T B q) :
    CoefficientBound (b.baseChange ℝ) T
      (A + (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
        ((((Fintype.card ι : ℝ) + 1) * (H + 1)) * A + B))
      (sectionCorrectedPolynomial φ S p q) := by
  apply (coefficientBound_iff_norm _ T hT (by positivity) _).mpr
  intro α
  exact sectionCorrectedPolynomial_coefficient_norm b c φ S hφ hS p q T A B α
    ((coefficientBound_iff_norm _ T hT hA p).mp hp α)
    ((coefficientBound_iff_norm _ T hT hB q).mp hq α)

theorem sectionCorrectedPolynomial_coefficientGrid
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) {l : ℕ} (hl : 0 < l)
    (hp : CoefficientGrid (b.baseChange ℝ) l p)
    (hq : CoefficientGrid (c.baseChange ℝ) l q) :
    CoefficientGrid (b.baseChange ℝ)
      (matrixDenominator (LinearMap.toMatrix c b S) *
        matrixDenominator (LinearMap.toMatrix b c φ) * l)
      (sectionCorrectedPolynomial φ S p q) := by
  intro α
  exact sectionCorrectedPolynomial_coefficient_grid b c φ S p q hl α (hp α) (hq α)

end LieModules

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {s : ℕ}

noncomputable def positiveUnivariate (v : Fin s → V) : VectorPolynomial Unit ℚ V :=
  ∑ d, monomial (Finsupp.single () (d.val + 1)) (v d)

theorem positiveUnivariate_coefficient (v : Fin s → V) (d : Fin s) :
    coefficients (positiveUnivariate v) (Finsupp.single () (d.val + 1)) = v d := by
  classical
  simp only [positiveUnivariate, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  rw [Finset.sum_eq_single d]
  · simp only [Finsupp.single_eq_same]
  · intro j _ hj
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hj
    apply Fin.ext
    have h := congrArg (fun α : Unit →₀ ℕ => α ()) heq
    simp only [Finsupp.single_eq_same] at h
    omega
  · simp

theorem positiveUnivariate_coefficient_eq_zero (v : Fin s → V) (α : Unit →₀ ℕ)
    (hα : ∀ d : Fin s, Finsupp.single () (d.val + 1) ≠ α) :
    coefficients (positiveUnivariate v) α = 0 := by
  classical
  simp only [positiveUnivariate, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  exact Finset.sum_eq_zero (fun d _ => Finsupp.single_eq_of_ne (hα d).symm)

theorem positiveUnivariate_zero (v : Fin s → V) : coefficients (positiveUnivariate v) 0 = 0 := by
  apply positiveUnivariate_coefficient_eq_zero
  intro d h
  have h' := congrArg (fun α : Unit →₀ ℕ => α ()) h
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at h'
  omega

theorem positiveUnivariate_coefficients_mem (v : Fin s → V) (U : (Unit →₀ ℕ) → Submodule ℚ V)
    (hv : ∀ d, v d ∈ U (Finsupp.single () (d.val + 1))) :
    ∀ α, coefficients (positiveUnivariate v) α ∈ U α := by
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    exact hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα)]
    exact (U α).zero_mem

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem positiveUnivariate_coefficientBound (b : Basis ι ℝ L) (v : Fin s → L)
    (T : Unit → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ d, ‖b.equivFun (v d)‖ ≤ M / monomialScale T (Finsupp.single () (d.val + 1))) :
    CoefficientBound b T M (positiveUnivariate v) := by
  apply (coefficientBound_iff_norm b T hT hM _).mpr
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    exact hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα),
      map_zero, norm_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem positiveUnivariate_coefficientGrid (b : Basis ι ℝ L) (v : Fin s → L) (l : ℕ)
    (hv : ∀ d, b.equivFun (v d) ∈ realDenominatorGrid l) :
    CoefficientGrid b l (positiveUnivariate v) := by
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    simpa only [Basis.equivFun_apply] using hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα)]
    refine ⟨0, ?_⟩
    ext i
    simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ ι V : Type*}

theorem coordinate_scalarAffine
    [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
    (f : V →ₗ[ℝ] ℝ) (r : ℚ) (h : σ → ℚ) (P : VectorPolynomial σ ℚ V) :
    coordinate f.toAddMonoidHom (weightedDilation (fun _ : σ => 1) r (translate h P)) =
      realAxisAffinePullback (fun i => (h i : ℝ)) (fun _ => (r : ℝ)) (coordinate f.toAddMonoidHom P) := by
  apply MvPolynomial.funext
  intro x
  have harg : (fun i => MvPolynomial.aeval x (scalarAffinePolynomial r h i)) =
      (fun i => (h i : ℝ) + (r : ℝ) * x i) := by
    funext i
    simp [scalarAffinePolynomial]
  rw [← coordinate_eval₂ f x, ← substitute_scalarAffinePolynomial, eval₂_substitute,
    harg, coordinate_eval₂, realAxisAffinePullback_eval]

theorem CoefficientBound.scalarAffine [Fintype σ]
    [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V] [IsScalarTower ℚ ℝ V]
    (b : Basis ι ℝ V) (T A : σ → ℝ) (hT : ∀ i, 0 < T i) (hA : ∀ i, 0 < A i)
    {M B : ℝ} {s : ℕ} {P : VectorPolynomial σ ℚ V}
    (hP : CoefficientBound b T M P) (hM : 0 ≤ M) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) s P) (r : ℚ) (h : σ → ℚ)
    (hphysical : ∀ i, |(h i : ℝ)| + |(r : ℝ)| * A i ≤ B * T i) :
    CoefficientBound b A (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * B ^ s)
      (weightedDilation (fun _ : σ => 1) r (translate h P)) := by
  intro α i
  let Q := coordinate (b.coord i).toAddMonoidHom P
  have hQdeg : Q.totalDegree ≤ s := (degreeLE_one_iff_basis_totalDegree b s P).mp hdegree i
  have hQcoeff : ∀ β, |Q.coeff β| ≤ M / monomialScale T β := by
    intro β
    simp only [Q, coeff_coordinate]
    change |b.repr (coefficients P β) i| ≤ M / monomialScale T β
    exact hP β i
  have hcard : (Q.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le Q hQdeg
  have hbound := realAxisAffinePullback_coeff_bound T A (fun j => (h j : ℝ)) (fun _ => (r : ℝ))
    hT hA Q hB hQcoeff hphysical hQdeg α
  have heq := congrArg (fun q : MvPolynomial σ ℝ => q.coeff α) (coordinate_scalarAffine (b.coord i) r h P)
  rw [coeff_coordinate] at heq
  change (b.coord i) (coefficients (weightedDilation (fun _ : σ => 1) r (translate h P)) α) = _ at heq
  change |(b.coord i) (coefficients (weightedDilation (fun _ : σ => 1) r (translate h P)) α)| ≤ _
  rw [heq]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (monomialScale_pos A hA α).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hM)
    (pow_nonneg (zero_le_one.trans hB) s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_outer_polynomial_product_bounds (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ qs rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
        qs.length ≤ k → rs.length ≤ k →
        (∀ q ∈ qs, q.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ r ∈ rs, r.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ q ∈ qs, CoefficientBound (b.baseChange ℝ) (fun _ => 1)
          (Real.exp ((p + 2) ^ a)) q.coord) →
        (∀ r ∈ rs, CoefficientGrid (b.baseChange ℝ) l r.coord) →
        CoefficientBound (b.baseChange ℝ) (fun _ => 1)
          (Real.exp ((p + C) ^ C)) qs.prod.coord ∧
        CoefficientGrid (b.baseChange ℝ) m rs.reverse.prod.coord := by
  obtain ⟨Cs, hCs, hslow⟩ := exists_formal_polynomial_product_bound s a k
  obtain ⟨Cr, hCr, hrat⟩ := exists_formal_polynomial_product_grid s k
  refine ⟨max Cs Cr, hCs.trans (le_max_left _ _), ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  have hbs : (p + Cs) ^ Cs ≤ (p + (max Cs Cr : ℕ)) ^ max Cs Cr :=
    shifted_power_self_mono hp (by omega) (le_max_left _ _)
  have hbr : (p + Cr) ^ Cr ≤ (p + (max Cs Cr : ℕ)) ^ max Cs Cr :=
    shifted_power_self_mono hp (by omega) (le_max_right _ _)
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ := hrat F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hbr), hlm, ?_⟩
  intro qs rs hqs hrs hqa hra hqb hrb
  constructor
  · have h := hslow F b ω hF H p hH hp hι hσ hHp hstructure
      (fun _ => 1) (fun _ => zero_lt_one) qs hqs hqa hqb
    intro α i
    exact (h α i).trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr hbs) (monomialScale_pos (fun _ => 1) (fun _ => zero_lt_one) α).le)
  · exact hgrid rs.reverse (by simpa only [List.length_reverse] using hrs)
      (fun r hr => hra r (List.mem_reverse.mp hr))
      (fun r hr => hrb r (List.mem_reverse.mp hr))

end Erdos3.NilpotentLieFiltration

end

end OAI
