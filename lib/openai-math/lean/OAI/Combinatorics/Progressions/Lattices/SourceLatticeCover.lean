import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

noncomputable def withLattice {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Λ : Subgroup D.filtration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold L s d :=
  { D with lattice := Λ, grid := N, grid_pos := hN, inner_grid := hin, outer_grid := hout }

theorem withLattice_geometry {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Λ : Subgroup D.filtration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p q : ℝ} (hD : D.GeometryComplexityLE p) (hpq : p ≤ q) (hNb : (N : ℝ) ≤ Real.exp q) :
    (D.withLattice Λ N hN hin hout).GeometryComplexityLE q :=
  ⟨hD.1.trans hpq, hNb, fun i j k => (hD.2.2.1 i j k).trans hpq,
    fun i j k => (hD.2.2.2 i j k).trans hpq⟩

theorem exists_native_image_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup E.filtration.Group,
        Λ ≤ E.lattice ∧ (Λ.subgroupOf E.lattice).Characteristic ∧
        (Λ.subgroupOf E.lattice).Normal ∧ (Λ.subgroupOf E.lattice).FiniteIndex ∧
        (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          (E.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
          Λ.map realificationHom ⊓
              (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ).range ≤
            (D.lattice.map realificationHom).map
              (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
  obtain ⟨c, _, hbudget⟩ := exists_image_cover_reconstruction_budget (bchIntegralDenominatorBound s) 0
  let P : Polynomial ℕ := Polynomial.X + 1 + (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ d e D E φ p hp hD hE hφ
  let t := p + 1
  have ht : 0 ≤ t := add_nonneg hp zero_le_one
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHt : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hdt : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have het : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  have hlt : (D.grid : ℝ) ≤ Real.exp t := hD.2.1.trans (Real.exp_le_exp.mpr hpt)
  have hmt : (E.grid : ℝ) ≤ Real.exp t := hE.2.1.trans (Real.exp_le_exp.mpr hpt)
  obtain ⟨A, Λ, hA, hAb, hΛ, hchar, hnormal, hfinite, hindex, hin, hout, hcover⟩ :=
    E.filtration.exists_image_lattice_cover D.basis E.basis φ D.lattice E.lattice
      D.grid E.grid H D.grid_pos E.grid_pos hH D.inner_grid E.inner_grid E.outer_grid
      (fun i j => rationalHeightLE_ceil_exp (hφ i j))
      (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  let a := imageLatticeLogBudget (bchIntegralDenominatorBound s) t
  have ha : 0 ≤ a := imageLatticeLogBudget_nonneg _ ht
  have hAt : (A : ℝ) ≤ Real.exp a :=
    (Nat.cast_le.mpr hAb).trans (imageLatticeBound_le_exp _ _ _ H D.grid E.grid ht hdt het hHt hlt hmt)
  have hprod : ((E.grid * A : ℕ) : ℝ) ≤ Real.exp (t + a) := by
    rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hmt hAt (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hN : 0 < (E.grid * A) * E.grid := Nat.mul_pos (Nat.mul_pos E.grid_pos hA) E.grid_pos
  have hNg : (((E.grid * A) * E.grid : ℕ) : ℝ) ≤ Real.exp (2 * t + a) := by
    calc
      _ = ((E.grid * A : ℕ) : ℝ) * (E.grid : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp (t + a) * Real.exp t := mul_le_mul hprod hmt (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hidx : (Λ.relIndex E.lattice : ℝ) ≤ Real.exp (t * (t + a)) := by
    apply (Nat.cast_le.mpr hindex).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right het (add_nonneg ht ha)
  obtain ⟨hq, hi, _⟩ := hbudget t ht
  have hsum : t + (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hfinal p hp
  have hcC : (t + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg _)) _)).trans hsum
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hidx.trans (Real.exp_le_exp.mpr (hi.trans hcC)), (E.grid * A) * E.grid, hN, hin, hout, ?_, hcover⟩
  exact E.withLattice_geometry Λ _ hN hin hout hE (hpt.trans htC)
    (hNg.trans (Real.exp_le_exp.mpr (hq.trans hcC)))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group)

noncomputable def lowerCoverLattice : Subgroup D.filtration.Group :=
  Λ.map (changeStep (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot
    D.filtration.lowerCentralSeries_eq_bot).toMonoidHom

theorem lowerCoverLattice_coordinates :
    bchSubgroupCoordinates D.basis (D.lowerCoverLattice hst Λ) =
      bchSubgroupCoordinates D.basis Λ :=
  bchSubgroupCoordinates_changeStep _ _ D.basis Λ

theorem lowerCoverLattice_forward :
    D.lowerCoverLattice hst Λ ≤ Λ.comap
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
        (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact hy

theorem lowerCoverLattice_backward :
    Λ ≤ (D.lowerCoverLattice hst Λ).comap
      (mapOfSteps (hL := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro x hx
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem lowerCoverLattice_le (hΛ : Λ ≤ (D.raiseStep hst).lattice) :
    D.lowerCoverLattice hst Λ ≤ D.lattice := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact D.raiseStep_lattice_back hst (hΛ hy)

variable (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)

noncomputable def loweredCover : RationalFilteredNilmanifold L s d :=
  D.withLattice (D.lowerCoverLattice hst Λ) N hN
    (by rw [D.lowerCoverLattice_coordinates]; exact hin)
    (by rw [D.lowerCoverLattice_coordinates]; exact hout)

theorem loweredCover_filtration : (D.loweredCover hst Λ N hN hin hout).filtration = D.filtration := rfl

theorem loweredCover_geometry {p q : ℝ} (hD : D.GeometryComplexityLE p)
    (hpq : p ≤ q) (hNb : (N : ℝ) ≤ Real.exp q) :
    (D.loweredCover hst Λ N hN hin hout).GeometryComplexityLE q :=
  D.withLattice_geometry _ _ _ _ _ hD hpq hNb

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix

theorem bchSubgroupCoordinates_comap_ofSteps
    {ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
    (b : Basis ι ℚ L) (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup M t hM)) :
    bchSubgroupCoordinates b (Γ.comap (mapOfSteps (hL := hL) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup M t hM) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup M t hM) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

namespace RationalFilteredNilmanifold

theorem exists_native_source_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.lattice ∧ (Λ.subgroupOf D.lattice).Characteristic ∧
        (Λ.subgroupOf D.lattice).Normal ∧ (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
          Λ ≤ E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 2 * R ^ 2 + (R + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d e D E φ p hp hD hE hφ
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  have hAb : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  let N₀ := E.grid * matrixDenominator A
  let Λ₀ := E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
  have hN₀ : 0 < N₀ := Nat.mul_pos E.grid_pos (matrixDenominator_pos A)
  have hgrid : scaledIntegerGrid N₀ ⊆ bchSubgroupCoordinates D.basis Λ₀ := by
    rw [bchSubgroupCoordinates_comap_ofSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot) D.basis E.basis φ E.lattice]
    intro x hx
    exact E.inner_grid (matrix_mulVec_fine_grid A E.grid hx)
  let r := p + (p + 2) ^ 3
  have hpr : p ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hr : 0 ≤ r := hp.trans hpr
  have hN₀b : (N₀ : ℝ) ≤ Real.exp r := by
    rw [show (N₀ : ℝ) = (E.grid : ℝ) * matrixDenominator A by exact Nat.cast_mul _ _]
    exact (mul_le_mul hE.2.1 hAb (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hNb, hin, hout⟩ :=
    D.filtration.exists_normal_cover_exp_quadratic D.basis D.lattice Λ₀
      D.grid N₀ D.grid_pos hN₀ D.inner_grid D.outer_grid hgrid hr
      (by simpa only [Fintype.card_fin] using hD.1.trans hpr)
      (hD.2.1.trans (Real.exp_le_exp.mpr hpr)) hN₀b
  have htotal : r + 2 * r ^ 2 + (r + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by nlinarith [sq_nonneg r, sq_nonneg (r + 2)]
  have hiC : 2 * r ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 2)]
  have hgC : (r + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg r]
  exact ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hiC),
    N, hN, hin, hout,
    D.withLattice_geometry Λ N hN hin hout hD (hpr.trans hrC)
      (hNb.trans (Real.exp_le_exp.mpr hgC)), htarget⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
