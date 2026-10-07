import OAI.Combinatorics.Progressions.Estimates.MarkedPureEvaluation

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

theorem exists_exact_source_lattice_cover {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hentries : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) :
    let Λ := D.lattice ⊓ E.lattice.comap (mapOfSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
    ∃ (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
      (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
      (N : ℝ) ≤ Real.exp ((p + 2) ^ 5) ∧
      (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + 2) ^ 5) := by
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  let N := D.grid * (E.grid * matrixDenominator A)
  let Λ := D.lattice ⊓ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
  have hN : 0 < N := Nat.mul_pos D.grid_pos (Nat.mul_pos E.grid_pos (matrixDenominator_pos A))
  have hDN : D.grid ∣ N := dvd_mul_right _ _
  have hEN : E.grid * matrixDenominator A ∣ N := dvd_mul_left _ _
  have hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ := by
    intro x hx
    change (⟨D.basis.equivFun.symm x⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨φ (D.basis.equivFun.symm x)⟩ : E.filtration.Group) ∈ E.lattice
    refine ⟨D.inner_grid (scaledIntegerGrid_subset_of_dvd hDN hx), ?_⟩
    apply (bchSubgroupCoordinates_repr E.basis E.lattice _).mp
    apply E.inner_grid
    apply linearMap_mem_scaledGrid D.basis E.basis φ.toLinearMap hEN
    simpa only [LinearEquiv.apply_symm_apply] using hx
  have hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N := by
    intro x hx
    exact denominatorGrid_subset_of_dvd hDN (D.outer_grid hx.1)
  have hA : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact ((rationalLogHeight_le_iff _ p).mp (hentries i j)).2.trans
      (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hNbound : (N : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
    have h := mul_le_mul hD.2.1 (mul_le_mul hE.2.1 hA (Nat.cast_nonneg _) (Real.exp_nonneg _))
      (by positivity) (Real.exp_nonneg _)
    have h' : (N : ℝ) ≤ Real.exp (p + (p + (p + 2) ^ 3)) := by
      simpa only [N, Nat.cast_mul, ← Real.exp_add] using h
    apply h'.trans (Real.exp_le_exp.mpr ?_)
    have hp3 : p ≤ (p + 2) ^ 3 := le_power_budget hp (by decide)
    calc
      p + (p + (p + 2) ^ 3) ≤ 3 * (p + 2) ^ 3 := by linarith
      _ ≤ (p + 2) ^ 2 * (p + 2) ^ 3 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = (p + 2) ^ 5 := by ring
  exact ⟨N, hN, hin, hout, hNbound,
    D.withLattice_geometry Λ N hN hin hout hD (le_power_budget hp (by decide)) hNbound⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}

noncomputable def withLattice (M : D.MultidegreeStructure bound)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    (D.withLattice Λ N hN hin hout).MultidegreeStructure bound where
  filtration := M.filtration
  ordinary := M.ordinary
  basis := M.basis

theorem withLattice_complexity (M : D.MultidegreeStructure bound)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p P : ℝ} (hM : M.ComplexityLE p) (hpP : p ≤ P)
    (hD : (D.withLattice Λ N hN hin hout).GeometryComplexityLE P) :
    (M.withLattice Λ N hN hin hout).ComplexityLE P :=
  ⟨hD, fun a j k => (hM.2 a j k).trans hpP⟩

end RationalFilteredNilmanifold.MultidegreeStructure

theorem exists_marked_evaluation_lattice (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r t d e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
      (M : D.MultidegreeStructure (mixedCorrelationDegree s))
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      (E : RationalFilteredNilmanifold (L ⧸ J) u e) {p : ℝ},
      0 ≤ p → M.ComplexityLE p → E.GeometryComplexityLE p → (t : ℝ) ≤ p →
      (∀ i j, rationalLogHeight
        (E.basis.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤ p) →
      ∃ (B : ℕ) (Λ : Subgroup D.filtration.Group) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ)
        (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B),
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ ≤ D.lattice ∧
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧
        (M.withLattice Λ B hB hin hout).ComplexityLE ((p + C) ^ C) ∧
        (∀ z : D.filtration.Group, z ∈ Λ →
          (⟨markedBaseEvaluation F v w marked t J hJ 0 z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
        (∀ z : D.filtration.Group, z ∈ Λ →
          IntegralVector (markedQuotientPhase F v w marked t z.coord)) ∧
        ∀ z : D.RealGroup, z ∈ (D.withLattice Λ B hB hin hout).realLattice →
          (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈
            E.realLattice := by
  obtain ⟨C, hC, hcover⟩ := RationalFilteredNilmanifold.exists_native_linear_target_cover (s + 1)
  refine ⟨C, hC, ?_⟩
  intro I L _ _ r t d e u F v w marked D M J hJ E p hp hM hE ht hφ hψ
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
  have hpC : p ≤ (p + C) ^ C := by
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + C) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ C)
  obtain ⟨B, Λ, hB, hin, hout, hbound, hΛ, hcoords, hgeom, hmap, hphase⟩ :=
    hcover D E (markedBaseEvaluation F v w marked t J hJ 0)
      (markedQuotientPhase F v w marked t).toLinearMap hp hM.1 hE ht hφ hψ
  refine ⟨B, Λ, hB, hin, hout, hbound, hΛ, hcoords,
    M.withLattice_complexity Λ B hB hin hout hM hpC hgeom, hmap, hphase, ?_⟩
  exact (D.withLattice Λ B hB hin hout).linearMap_real_lattice E
    (markedBaseEvaluation F v w marked t J hJ 0) hmap

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d) (m : ℕ)

noncomputable def normalizedMarkedLattice : Subgroup D.filtration.Group :=
  D.lattice ⊓ (RationalTorus.nilmanifold t).lattice.comap
    (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
      (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot)
      (normalizedMarkedPhase F v w marked t m))

theorem normalizedMarkedLattice_le : normalizedMarkedLattice F v w marked t D m ≤ D.lattice :=
  inf_le_left

theorem normalizedMarkedLattice_integral (z : D.filtration.Group)
    (hz : z ∈ normalizedMarkedLattice F v w marked t D m) :
    IntegralVector (normalizedMarkedPhase F v w marked t m z.coord) := hz.2

theorem normalizedMarkedLattice_direction (hm : 0 < m) (a : Fin t → ℤ)
    (ha : (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
      D.filtration.Group) ∈ D.lattice) :
    (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
      D.filtration.Group) ∈ normalizedMarkedLattice F v w marked t D m := by
  refine ⟨ha, ?_⟩
  change IntegralVector (normalizedMarkedPhase F v w marked t m
    ((m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))))
  rw [normalizedMarkedPhase_scaled_direction F v w marked t m hm]
  exact ⟨a, fun _ => rfl⟩

theorem exists_normalizedMarkedLattice_model
    (M : D.MultidegreeStructure (mixedCorrelationDegree s)) {p : ℝ}
    (hp : 0 ≤ p) (hM : M.ComplexityLE p) (ht : (t : ℝ) ≤ p) (hm : 0 < m)
    (hmp : (m : ℝ) ≤ Real.exp p)
    (hcoords : ∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤ p) :
    ∃ (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis (normalizedMarkedLattice F v w marked t D m))
      (hout : bchSubgroupCoordinates D.basis (normalizedMarkedLattice F v w marked t D m) ⊆ denominatorGrid N),
      (N : ℝ) ≤ Real.exp ((2 * p + 3) ^ 5) ∧
      (M.withLattice (normalizedMarkedLattice F v w marked t D m) N hN hin hout).ComplexityLE
        ((2 * p + 3) ^ 5) := by
  have hpP : p ≤ 2 * p + 1 := by linarith
  have hP : 0 ≤ 2 * p + 1 := hp.trans hpP
  have hentries (i j) : rationalLogHeight ((RationalTorus.nilmanifold t).basis.repr
      (normalizedMarkedPhase F v w marked t m (D.basis j)) i) ≤ 2 * p + 1 := by
    change rationalLogHeight ((RationalTorus.basis t).repr
      (normalizedMarkedPhase F v w marked t m (D.basis j)) i) ≤ _
    rw [RationalTorus.basis_repr]
    exact normalizedMarkedPhase_height F v w marked t m hm hp hmp (D.basis j) i (hcoords i j)
  obtain ⟨N, hN, hin, hout, hNbound, hgeom⟩ := D.exists_exact_source_lattice_cover
    (RationalTorus.nilmanifold t) (normalizedMarkedPhase F v w marked t m) hP
    (hM.1.mono D hpP) (RationalTorus.nilmanifold_geometry t hP (ht.trans hpP)) hentries
  have heq : 2 * p + 1 + 2 = 2 * p + 3 := by ring
  rw [heq] at hNbound hgeom
  have hpQ : p ≤ (2 * p + 3) ^ 5 := hpP.trans (by
    simpa only [heq] using le_power_budget hP (by decide : 1 ≤ 5))
  exact ⟨N, hN, hin, hout, hNbound,
    M.withLattice_complexity (normalizedMarkedLattice F v w marked t D m)
      N hN hin hout hM hpQ hgeom⟩

end Erdos3

end

end OAI
