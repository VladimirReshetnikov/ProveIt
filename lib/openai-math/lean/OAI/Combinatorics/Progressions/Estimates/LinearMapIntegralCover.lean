import OAI.Combinatorics.Progressions.Nilpotent.NativeCoverNiltest

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_native_integral_model_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ (B : ℕ) (Λ : Subgroup D.filtration.Group) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ)
        (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B),
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ ≤ D.lattice ∧
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧
        (D.withLattice Λ B hB hin hout).GeometryComplexityLE ((p + C) ^ C) := by
  obtain ⟨c, _, hcover⟩ := exists_integral_grid_subgroup_exp s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + 1 + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  have hp1 : p ≤ p + 1 := by linarith
  have hbud : p + (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcC : (p + 1 + c) ^ c ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by
    have hn : 0 ≤ (p + 1 + c) ^ c := by positivity
    linarith
  obtain ⟨B, Λ, hB, _, hBb, hΛ, hcoords⟩ :=
    hcover D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid ⌈Real.exp p⌉₊
      (p + 1) D.grid_pos
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) D.inner_grid
      (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans hp1)
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr hp1))
  have hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ := hcoords.symm.le
  have hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B := by
    rw [hcoords]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx
  have hBC : (B : ℝ) ≤ Real.exp ((p + C) ^ C) := hBb.trans (Real.exp_le_exp.mpr hcC)
  exact ⟨B, Λ, hB, hin, hout, hBC, hΛ, hcoords,
    D.withLattice_geometry Λ B hB hin hout hD hpC hBC⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct

theorem linearMap_mem_scaledGrid {L M ι κ : Type*}
    [AddCommGroup L] [Module ℚ L] [AddCommGroup M] [Module ℚ M]
    [Fintype ι] [Fintype κ] [DecidableEq ι] (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) {a b : ℕ}
    (hab : b * matrixDenominator (LinearMap.toMatrix e f φ) ∣ a)
    {x : L} (hx : e.equivFun x ∈ scaledIntegerGrid a) :
    f.equivFun (φ x) ∈ scaledIntegerGrid b := by
  classical
  have h := matrix_mulVec_fine_grid (LinearMap.toMatrix e f φ) b
    (scaledIntegerGrid_subset_of_dvd hab hx)
  change LinearMap.toMatrix e f φ *ᵥ e.equivFun x ∈ scaledIntegerGrid b at h
  have hmap : LinearMap.toMatrix e f φ *ᵥ e.equivFun x = f.equivFun (φ x) := by
    simpa only [Basis.equivFun_apply] using LinearMap.toMatrix_mulVec_repr e f φ x
  rwa [hmap] at h

namespace RationalFilteredNilmanifold

theorem linearMap_real_lattice {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ[ℚ] M)
    (hφ : ∀ z : D.filtration.Group, z ∈ D.lattice →
      (⟨φ z.coord⟩ : E.filtration.Group) ∈ E.lattice)
    (z : D.RealGroup) (hz : z ∈ D.realLattice) :
    (⟨φ.baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice := by
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨⟨φ x.coord⟩, hφ x hx, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change (1 : ℝ) ⊗ₜ[ℚ] φ x.coord = φ.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] x.coord)
  exact (LinearMap.baseChange_tmul _ _ _).symm

theorem exists_native_linear_target_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {t d e k : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (φ : L →ₗ[ℚ] M) (ψ : L →ₗ[ℚ] (Fin k → ℚ)) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p → (k : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (ψ (D.basis j) i) ≤ p) →
      ∃ (B : ℕ) (Λ : Subgroup D.filtration.Group) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ)
        (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B),
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ ≤ D.lattice ∧
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧
        (D.withLattice Λ B hB hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ z : D.filtration.Group, z ∈ Λ → (⟨φ z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
        ∀ z : D.filtration.Group, z ∈ Λ → IntegralVector (ψ z.coord) := by
  obtain ⟨a, _, hcover⟩ := exists_integral_grid_subgroup_exp s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := 2 * X + 2 * (X + 2) ^ 3 + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ t d e k D E φ ψ p hp hD hE hk hφ hψ
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ
  let Z := LinearMap.toMatrix D.basis (Pi.basisFun ℚ (Fin k)) ψ
  let l := D.grid * ((E.grid * matrixDenominator A) * matrixDenominator Z)
  let P := 2 * p + 2 * (p + 2) ^ 3 + 1
  have hp1 : p + 1 ≤ P := by dsimp [P]; nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) 3]
  have hpP : p ≤ P := (by linarith : p ≤ p + 1).trans hp1
  have hP : 0 ≤ P := hp.trans hpP
  have hA : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hZ : (matrixDenominator Z : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power Z hp 1
      (by simpa only [Fintype.card_fin] using hk)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hψ i j)).2
    dsimp only [Z]
    rw [LinearMap.toMatrix_apply]
    simp only [Pi.basisFun_repr]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hl : 0 < l := Nat.mul_pos D.grid_pos
    (Nat.mul_pos (Nat.mul_pos E.grid_pos (matrixDenominator_pos A)) (matrixDenominator_pos Z))
  have hDl : D.grid ∣ l := dvd_mul_right _ _
  have hAl : E.grid * matrixDenominator A ∣ l :=
    dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have hZl : matrixDenominator Z ∣ l :=
    dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hlP : (l : ℝ) ≤ Real.exp P := by
    have h := mul_le_mul hD.2.1
      (mul_le_mul (mul_le_mul hE.2.1 hA (Nat.cast_nonneg _) (Real.exp_nonneg _)) hZ
        (Nat.cast_nonneg _) (by positivity)) (by positivity) (Real.exp_nonneg _)
    change (D.grid : ℝ) * ((E.grid : ℝ) * matrixDenominator A * matrixDenominator Z) ≤ _ at h
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add] at h
    have h' : (l : ℝ) ≤ Real.exp (p + (p + (p + 2) ^ 3 + (p + 2) ^ 3)) := by
      simpa only [l, Nat.cast_mul] using h
    apply h'.trans
    apply Real.exp_le_exp.mpr
    dsimp only [P]
    ring_nf
    linarith
  have hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates D.basis D.lattice :=
    fun _ hx => D.inner_grid (scaledIntegerGrid_subset_of_dvd hDl hx)
  obtain ⟨B, Λ, hB, hlB, hBP, hΛ, hcoords⟩ :=
    hcover D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice l ⌈Real.exp p⌉₊ P hl
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) hinner hP
      (by simpa only [Fintype.card_fin] using hD.1.trans hpP)
      ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1)) hlP
  have hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ := hcoords.symm.le
  have hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B := by
    rw [hcoords]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx
  have htotal : P + (P + a) ^ a ≤ (p + C) ^ C := by
    simpa [P₀, X, P, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (P + a) ^ a ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  have hpC : p ≤ (p + C) ^ C := hpP.trans
    ((le_add_of_nonneg_right (by positivity : 0 ≤ (P + a) ^ a)).trans htotal)
  have hBC : (B : ℝ) ≤ Real.exp ((p + C) ^ C) := hBP.trans (Real.exp_le_exp.mpr haC)
  refine ⟨B, Λ, hB, hin, hout, hBC, hΛ, hcoords,
    D.withLattice_geometry Λ B hB hin hout hD hpC hBC, ?_, ?_⟩
  · intro z hz
    apply (bchSubgroupCoordinates_repr E.basis E.lattice ⟨φ z.coord⟩).mp
    apply E.inner_grid
    apply linearMap_mem_scaledGrid D.basis E.basis φ (hAl.trans hlB)
    rw [← hcoords]
    exact (bchSubgroupCoordinates_repr D.basis Λ z).mpr hz
  · intro z hz
    have hgrid : D.basis.equivFun z.coord ∈ scaledIntegerGrid B := by
      rw [← hcoords]
      exact (bchSubgroupCoordinates_repr D.basis Λ z).mpr hz
    have h := linearMap_mem_scaledGrid D.basis (Pi.basisFun ℚ (Fin k)) ψ (b := 1)
      (by simpa only [one_mul] using hZl.trans hlB) hgrid
    obtain ⟨v, hv⟩ := h
    exact ⟨v, fun i => by simpa only [Nat.cast_one, one_smul, Basis.equivFun_apply,
      Pi.basisFun_repr] using congrFun hv i⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
