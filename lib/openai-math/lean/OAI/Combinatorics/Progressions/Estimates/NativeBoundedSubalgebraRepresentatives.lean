import OAI.Combinatorics.Progressions.Dynamics.LieSubalgebraRepresentativeBudget
import OAI.Combinatorics.Progressions.Lattices.LieSubalgebraLatticeInnerGrid
import OAI.Combinatorics.Progressions.Linear.RefilteredKernelConstantBounds

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_native_subalgebra_rational_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ L : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (K : LieSubalgebra ℚ L)
      (bk : Basis κ ℚ K) (l H : ℕ) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      0 < l →
      scaledIntegerGrid l ⊆ bchSubgroupCoordinates bk
        (D.lattice.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot
          D.filtration.lowerCentralSeries_eq_bot K) K.incl)) →
      (∀ i j k, RationalHeightLE (lieStructureConstants bk i j k) H) →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j, |(D.basis.repr (bk j : L) i : ℝ)| ≤ Real.exp p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup, g ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          ∃ r : D.RealGroup, r ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K ∧
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ := by
  obtain ⟨a, _, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hclosure⟩ := exists_real_bch_rational_closure s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a + 2 * X + (2 * X + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro κ L _ _ _ _ _ _ _ d D K bk l H p hp hD hκ hl hinner hc hH hlp hentries q hq hqp
  classical
  let t := 2 * p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let H0 := ⌈Real.exp p⌉₊
  have hH0 : (H0 : ℝ) ≤ Real.exp t := (ceil_exp_le_exp_add_one hp).trans
    (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ t by dsimp [t]; linarith)
  have hc0 : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H0 :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hprod : ((q * D.grid : ℕ) : ℝ) ≤ Real.exp t := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hqp hD.2.1 (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨m, hm, hmb, _, hmul, _⟩ := hclosure D.basis H0 t
    D.filtration.lowerCentralSeries_eq_bot ht hd hH0 hc0 (q * D.grid)
    (Nat.mul_pos hq D.grid_pos) hprod
  have hsum : (p + a) ^ a + 2 * p + (t + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a + 2 * p ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (t + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + a) ^ a + 2 * p)).trans hsum
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hgK hg
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let hnilK := lie_subalgebra_lowerCentralSeries_eq_bot D.filtration.lowerCentralSeries_eq_bot K
  let f := realificationMap (hnil := hnilK) (hM := D.filtration.lowerCentralSeries_eq_bot) K.incl
  obtain ⟨gK, hgK⟩ := (show g ∈ f.range from by
    rwa [realificationMap_incl_range])
  obtain ⟨rK, hrK, γK, hγK, hfac⟩ := hrep bk hnilK
    (D.lattice.comap (map K.incl)) l H p hl hinner hc hp hκ hH hlp gK
  have hγ : f γK ∈ D.realLattice := by
    change γK ∈ D.realLattice.comap f
    dsimp only [realLattice, f]
    rw [realification_subgroup_comap_incl]
    exact hγK
  have heq : g = f rK * f γK := by rw [← hgK, hfac, map_mul]
  refine ⟨f rK, realificationMap_incl_mem K rK, ?_, ?_, f γK, hγ, heq⟩
  · intro i
    change |(D.basis.baseChange ℝ).repr (K.incl.toLinearMap.baseChange ℝ rK.coord) i| ≤ _
    rw [scalarExtension_coordinate_sum D.basis bk K.incl.toLinearMap rK.coord i]
    calc
      _ ≤ ∑ j, |(bk.baseChange ℝ).repr rK.coord j * (D.basis.repr (K.incl (bk j)) i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : κ, Real.exp ((p + a) ^ a) * Real.exp p := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hrK j) (hentries i j) (abs_nonneg _) (Real.exp_pos _).le
      _ = (Fintype.card κ : ℝ) * (Real.exp ((p + a) ^ a) * Real.exp p) := by simp
      _ ≤ Real.exp p * (Real.exp ((p + a) ^ a) * Real.exp p) := by
        exact mul_le_mul_of_nonneg_right (hκ.trans (by linarith [Real.add_one_le_exp p])) (by positivity)
      _ = Real.exp ((p + a) ^ a + 2 * p) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr haC
  · have hγgrid := realification_subgroup_grid D.basis D.lattice D.grid D.outer_grid
      (f γK)⁻¹ (D.realLattice.inv_mem hγ)
    have h := hmul g (f γK)⁻¹
      (realDenominatorGrid_subset_of_dvd hq (dvd_mul_right q D.grid) hg)
      (realDenominatorGrid_subset_of_dvd D.grid_pos (dvd_mul_left D.grid q) hγgrid)
    simpa only [heq, mul_inv_cancel_right] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_bounded_subalgebra_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ L : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (K : LieSubalgebra ℚ L)
      (bk : Basis κ ℚ K) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (bk j : L) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup,
          g ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          ∃ r : D.RealGroup,
            r ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K ∧
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ := by
  obtain ⟨a, _, hrep⟩ := exists_native_subalgebra_rational_representatives s
  let P : Polynomial ℕ := ((Polynomial.X + 3) ^ 12 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro κ L _ _ _ _ _ _ _ d D K bk p hp hD hκ hinc q hq hqp
  classical
  let H := ⌈Real.exp p⌉₊
  let p0 := p + 1
  let t := lieSubalgebraRepresentativeParameter p0
  have hp0 : 0 ≤ p0 := by dsimp [p0]; positivity
  have hpt : p ≤ t := (show p ≤ p0 by dsimp [p0]; linarith).trans
    (le_power_budget hp0 (by decide : 1 ≤ 12))
  have ht : 0 ≤ t := (lieSubalgebraRepresentativeParameter_pos hp0).le
  have hd0 : (Fintype.card (Fin d) : ℝ) ≤ p0 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p0 by dsimp [p0]; linarith)
  have hκ0 : (Fintype.card κ : ℝ) ≤ p0 := hκ.trans (by dsimp [p0]; linarith)
  have hH : (H : ℝ) ≤ Real.exp p0 := ceil_exp_le_exp_add_one hp
  have hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hincH : ∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H :=
    fun i j => rationalHeightLE_ceil_exp (hinc i j)
  let HC := lieSubalgebraRepresentativeHeight (Fintype.card (Fin d)) (Fintype.card κ) H
  have hHC : (HC : ℝ) ≤ Real.exp t :=
    lieSubalgebraRepresentativeHeight_le_exp_parameter _ _ _ hp0 hd0 hκ0 hH
  have hcK : ∀ i j k, RationalHeightLE (lieStructureConstants bk i j k) HC :=
    lieSubalgebraRepresentative_bracket_height D.basis K bk (one_le_ceil_exp p) hc hincH
  let A : Matrix (Fin d) κ ℚ := fun i j => D.basis.repr (bk j : L) i
  let qI := matrixDenominator A
  have hqI : 0 < qI := matrixDenominator_pos A
  have hcolumns : ∀ j, D.basis.equivFun (bk j : L) ∈ denominatorGrid qI := by
    intro j
    refine ⟨fun i => clearedMatrix A i j, fun i => ?_⟩
    exact (congrFun (congrFun (clearedMatrix_cast A) i) j).symm
  have hqIb : (qI : ℝ) ≤ Real.exp ((p0 + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp0 1 hd0 hκ0
    intro i j
    exact ((Nat.cast_le.mpr (hincH i j).2).trans hH).trans
      (Real.exp_le_exp.mpr (le_power_budget hp0 (by decide : 1 ≤ 1)))
  have hlb : ((D.grid * qI : ℕ) : ℝ) ≤ Real.exp t := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p0 * Real.exp ((p0 + 2) ^ 3) :=
        mul_le_mul (hD.2.1.trans (Real.exp_le_exp.mpr (by dsimp [p0]; linarith)))
          hqIb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (p0 + (p0 + 2) ^ 3) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p0 + 2) ^ 4) := by
        apply Real.exp_le_exp.mpr
        have hpow := le_power_budget hp0 (by decide : 1 ≤ 3)
        have hnon : 0 ≤ (p0 + 2) ^ 3 := by positivity
        rw [pow_succ]
        nlinarith
      _ ≤ _ := Real.exp_le_exp.mpr
        (pow_le_pow_right₀ (by linarith : 1 ≤ p0 + 2) (by decide : 4 ≤ 12))
  have hinner := lieSubalgebra_comap_inner_grid_of_columns K bk D.basis D.lattice
    D.grid qI D.inner_grid hcolumns
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D K bk (D.grid * qI) HC t ht (GeometryComplexityLE.mono D hD hpt)
    (hκ.trans hpt) (Nat.mul_pos D.grid_pos hqI) hinner hcK hHC hlb
    (fun i j => ((hincH i j).abs_real_le.trans hH).trans
      (Real.exp_le_exp.mpr (le_power_budget hp0 (by decide : 1 ≤ 12))))
    q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  have hb : (t + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, t, lieSubalgebraRepresentativeParameter, p0, Polynomial.eval₂_pow, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num]
      using hbudget p hp
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hb), ?_⟩
  intro g hgK hg
  obtain ⟨r, hrK, hr, hrgrid, γ, hγ, hfac⟩ := hreps g hgK hg
  exact ⟨r, hrK, fun i => (hr i).trans (Real.exp_le_exp.mpr hb), hrgrid, γ, hγ, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
