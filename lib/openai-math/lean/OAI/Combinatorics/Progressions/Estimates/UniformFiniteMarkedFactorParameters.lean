import OAI.Combinatorics.Progressions.Dynamics.FilteredSectionSingleDenominatorBudget
import OAI.Combinatorics.Progressions.Lattices.RefilteredResidueExpansionSpec
import OAI.Combinatorics.Progressions.Linear.ActualMarkedSlowKernelCells
import OAI.Combinatorics.Progressions.Sampling.BoundedKernelGridEnumerationBudget
import OAI.Combinatorics.Progressions.Sampling.MarkedKernelRationalGrid

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def MarkedRationalFactorFreezing
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (B : ℝ) : Prop :=
  ∃ M m : ℕ, 0 < M ∧ 0 < m ∧ (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧
    ∀ (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
      (RF : (F.realification.adaptedPolynomialFiltration w).Group),
      D.filtration.PolynomialRationalGrid D.basis w l R →
      F.PolynomialRationalGrid c w l RF →
      D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
      ∃ r : (σ → ZMod M) → D.RealGroup,
        (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := F.lowerCentralSeries_eq_bot) φ (r a) = 1 ∧
          (∀ i, |(D.basis.baseChange ℝ).repr (r a).coord i| ≤ B) ∧
          (D.basis.baseChange ℝ).equivFun (r a).coord ∈ realDenominatorGrid m) ∧
        ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
          D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
              ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R) =
            r (fun j => (x j : ZMod M)) * γ ∧
          D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) R =
            D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                (D.filtration.filteredRealPolynomialSection F w S hS RF) *
              r (fun j => (x j : ZMod M)) * γ

theorem exists_native_marked_rational_factor_freezing_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
      (w : σ → ℕ), (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∀ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
      Function.RightInverse S φ →
      (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
        (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      D.MarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) := by
  obtain ⟨a, _, hgrid⟩ := NilpotentLieFiltration.exists_marked_kernel_rational_grid_bound s
  obtain ⟨b, _, hreps⟩ := exists_native_marked_kernel_residue_representatives s
  let U : Polynomial ℕ := (Polynomial.X + 3) ^ 11
  let V : Polynomial ℕ := (U + Polynomial.C a) ^ a + U
  let P : Polynomial ℕ := (V + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ d t D F c ω hlayers φ hφ w hw p hp hD hσ hκ hφb
    S hS hright hSb l hl hlp
  classical
  let p0 := p + 1
  let u := (p0 + 2) ^ 11
  let v := (u + a) ^ a + u
  let H := ⌈Real.exp p⌉₊
  have hp0 : 0 ≤ p0 := by dsimp [p0]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpu : p ≤ u := (show p ≤ p0 by dsimp [p0]; linarith).trans
    (le_power_budget hp0 (by decide : 1 ≤ 11))
  have huv : u ≤ v := le_add_of_nonneg_left (by positivity)
  have hpv : p ≤ v := hpu.trans huv
  have hv : 0 ≤ v := hu.trans huv
  have hd0 : (Fintype.card (Fin d) : ℝ) ≤ p0 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p0 by dsimp [p0]; linarith)
  have hκ0 : (Fintype.card κ : ℝ) ≤ p0 := hκ.trans (by dsimp [p0]; linarith)
  have hH : (H : ℝ) ≤ Real.exp p0 := ceil_exp_le_exp_add_one hp
  have hφH : ∀ i j, RationalHeightLE (c.repr (φ (D.basis j)) i) H :=
    fun i j => rationalHeightLE_ceil_exp (hφb i j)
  have hden : ((matrixDenominator (LinearMap.toMatrix c D.basis S) * l : ℕ) : ℝ) ≤
      Real.exp u := by
    apply filtered_section_single_denominator_le_exp
      (LinearMap.toMatrix D.basis c φ.toLinearMap) (LinearMap.toMatrix c D.basis S) l
      hp0 hd0 hκ0 hH
    · intro i j
      rw [LinearMap.toMatrix_apply]
      exact hφH i j
    · simpa only [LinearMap.toMatrix_apply] using hSb
    · exact hlp.trans (Real.exp_le_exp.mpr (by dsimp [p0]; linarith))
  have hHpu : (H : ℝ) ≤ Real.exp u := hH.trans
    (Real.exp_le_exp.mpr (le_power_budget hp0 (by decide : 1 ≤ 11)))
  obtain ⟨q, hq, hqb, _, hqgrid⟩ := hgrid D.filtration F D.basis c ω hlayers w hw H u
    (one_le_ceil_exp p) hu (by simpa only [Fintype.card_fin] using hD.1.trans hpu)
    (hσ.trans hpu) hHpu (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    S hS l hl hden
  have hqv : (q : ℝ) ≤ Real.exp v := hqb.trans
    (Real.exp_le_exp.mpr (le_add_of_nonneg_right hu))
  obtain ⟨M, m, hM, hm, hMb, hmb, hfreeze⟩ := hreps D F c φ w hw v hv
    (GeometryComplexityLE.mono D hD hpv) (hσ.trans hpv) (hκ.trans hpv)
    (fun i j => (hφb i j).trans hpv) q hq hqv
  have hb : (v + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, V, U, v, u, p0, Polynomial.eval₂_pow, add_assoc,
      show (1 : ℝ) + 2 = 3 by norm_num] using hbudget p hp
  refine ⟨M, m, hM, hm, hMb.trans (Real.exp_le_exp.mpr hb),
    hmb.trans (Real.exp_le_exp.mpr hb), ?_⟩
  intro R RF hR hRF hmark
  let KR := (D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R
  have hKR : D.filtration.realPolynomialGroupMap F φ hφ w KR = 1 := by
    dsimp only [KR]
    rw [map_mul, map_inv, hmark,
      D.filtration.realPolynomialGroupMap_filteredSection F w φ hφ S hS hright RF,
      inv_mul_cancel]
  have hpoint (x : σ → ℤ) : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ
      (D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) KR) = 1 := by
    rw [← D.filtration.realPolynomialGroupMap_value F φ hφ w, hKR, map_one]
  obtain ⟨r, hr, hfac⟩ := hfreeze KR (hqgrid R RF hR hRF) hpoint
  refine ⟨r, fun z => ⟨(hr z).1, fun i => ((hr z).2.1 i).trans
    (Real.exp_le_exp.mpr hb), (hr z).2.2⟩, ?_⟩
  intro x
  obtain ⟨γ, hγ, heq⟩ := hfac x
  refine ⟨γ, hγ, heq, ?_⟩
  have heq' := heq
  dsimp only [KR] at heq'
  rw [map_mul, map_inv] at heq'
  calc
    _ = D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
        (D.filtration.filteredRealPolynomialSection F w S hS RF) *
        (r (fun j => (x j : ZMod M)) * γ) := by
      rw [← heq']
      group
    _ = _ := (mul_assoc _ _ _).symm

theorem exists_native_marked_rational_factor_freezing (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          D.MarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_native_marked_rational_factor_freezing_bound s
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hright, hS, hSb⟩ := D.filtration.exists_bounded_filtered_section F D.basis ω
    hDlayers c τ hFlayers φ.toLinearMap hsurj (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hφb i j))
  exact ⟨S, hS, hright, hSb,
    hfreeze D F c ω hDlayers φ hφ w hw p hp hD hσ hκ hφb S hS hright hSb⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem MarkedRationalFactorFreezing.finite_enumeration
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) {B p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hB : B ≤ Real.exp p)
    (hfreeze : D.MarkedRationalFactorFreezing F c φ hφ w S hS l B) :
    ∃ M m n : ℕ, 0 < M ∧ 0 < m ∧ 0 < n ∧
      (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∃ center : Fin n → D.RealGroup,
        (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := F.lowerCentralSeries_eq_bot) φ (center a) = 1 ∧
          (∀ i, |(D.basis.baseChange ℝ).repr (center a).coord i| ≤ B) ∧
          (D.basis.baseChange ℝ).equivFun (center a).coord ∈ realDenominatorGrid m) ∧
        ∀ (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
          (RF : (F.realification.adaptedPolynomialFiltration w).Group),
          D.filtration.PolynomialRationalGrid D.basis w l R →
          F.PolynomialRationalGrid c w l RF →
          D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
          ∃ label : (σ → ZMod M) → Fin n,
            ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                  ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R) =
                center (label (fun j => (x j : ZMod M))) * γ ∧
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) R =
                D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                    (D.filtration.filteredRealPolynomialSection F w S hS RF) *
                  center (label (fun j => (x j : ZMod M))) * γ := by
  classical
  obtain ⟨M, m, hM, hm, hMb, hmb, hfactor⟩ := hfreeze
  have hB0 : 0 ≤ B := (Nat.cast_nonneg m).trans hmb
  obtain ⟨n, hn, hnb, center, hcenters, hcover⟩ :=
    exists_bounded_kernel_grid_enumeration_exp (D.basis.baseChange ℝ)
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) φ) m hm hp hB0
      (by simpa only [Fintype.card_fin] using hd) (hmb.trans hB) hB
  refine ⟨M, m, n, hM, hm, hn, hMb, hmb, hnb, center, hcenters, ?_⟩
  intro R RF hR hRF hmark
  obtain ⟨r, hr, hfac⟩ := hfactor R RF hR hRF hmark
  choose label hlabel using fun a => hcover (r a) (hr a).1 (hr a).2.1 (hr a).2.2
  refine ⟨label, ?_⟩
  intro x
  obtain ⟨γ, hγ, hKR, hRfac⟩ := hfac x
  refine ⟨γ, hγ, ?_, ?_⟩
  · simpa only [hlabel] using hKR
  · simpa only [hlabel] using hRfac

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

theorem MarkedRationalFactorFreezing.mono
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {B B' : ℝ}
    (h : D.MarkedRationalFactorFreezing F c φ hφ w S hS l B) (hBB' : B ≤ B') :
    D.MarkedRationalFactorFreezing F c φ hφ w S hS l B' := by
  obtain ⟨M, m, hM, hm, hMB, hmB, hfreeze⟩ := h
  refine ⟨M, m, hM, hm, hMB.trans hBB', hmB.trans hBB', ?_⟩
  intro R RF hR hRF hmark
  obtain ⟨r, hr, hfac⟩ := hfreeze R RF hR hRF hmark
  exact ⟨r, fun a => ⟨(hr a).1, fun i => ((hr a).2.1 i).trans hBB', (hr a).2.2⟩,
    hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def MarkedSlowFactorFreezing
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  ∃ N Q : ℕ, 0 < N ∧ 0 < Q ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    ∃ center : (Fin d → Fin (N + 1)) → D.RealGroup,
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) φ (center j) = 1) ∧
      (∀ j i, |(D.basis.baseChange ℝ).repr (center j).coord i| ≤ B) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        ∃ label : (σ → Fin (Q + 1)) → (Fin d → Fin (N + 1)),
          ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ Tbox i) →
            (∀ i, |v i - normalizedRealBoxGrid Tbox Q j i| ≤ Tbox i * (2 / Q)) →
            dist (D.filtration.adaptedPolynomialRealValueHom w v
              (E * (D.filtration.filteredRealPolynomialSection F w S hS EF)⁻¹))
              (center (label j)) ≤ ε

theorem exists_uniform_marked_factor_parameters (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.MarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) ∧
            D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨A, _, hrat⟩ := exists_native_marked_rational_factor_freezing s
  obtain ⟨B, _, hslow⟩ := NilpotentLieFiltration.exists_actual_marked_slow_kernel_cells s (max a 7) u
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A +
    (Polynomial.X + 1 + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  classical
  obtain ⟨S, hS, hright, hSb, hratS⟩ := hrat D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  have hsum : (p + A) ^ A + (p + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hA : (p + A) ^ A ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (p + 1 + B) ^ B)).trans hsum
  have hB : (p + 1 + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + A) ^ A)).trans hsum
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT
  refine ⟨(hratS l hl hlp).mono (Real.exp_le_exp.mpr hA), ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let H := ⌈Real.exp p⌉₊
  have hp1 : 0 ≤ p + 1 := by positivity
  have hp_le : p ≤ p + 1 := by linarith
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hK := rationalKernelHeight_le_budget (Fintype.card κ) H hp1 (hκ.trans hp_le) hH
  have hentry : ∀ i j, |(D.basis.repr (S (c j)) i : ℝ)| ≤
      Real.exp (((p + 1) + 2) ^ max a 7) := by
    intro i j
    apply ((hSb i j).abs_real_le.trans hK).trans
    apply Real.exp_le_exp.mpr
    exact pow_le_pow_right₀ (by linarith : 1 ≤ (p + 1) + 2) (le_max_right _ _)
  obtain ⟨N, Q, hN, hQ, hNcard, hQcard, center, hmark, hcap, hfreeze⟩ :=
    hslow D.filtration F D.basis c ω hDlayers w hw φ hφ S hS hright H (p + 1)
      (one_le_ceil_exp p) hp1 (by simpa only [Fintype.card_fin] using hD.1.trans hp_le)
      (hκ.trans hp_le) (hσ.trans hp_le) hH
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) hentry Tbox hT
  refine ⟨N, Q, hN, hQ, hNcard.trans (Real.exp_le_exp.mpr hB),
    hQcard.trans (Real.exp_le_exp.mpr hB), center, hmark,
    fun j i => (hcap j i).trans (Real.exp_le_exp.mpr hB), ?_⟩
  intro E EF hE hEF hproj
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp (((p + 1) + 2) ^ max a 7) := by
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2)
      (by linarith : p + 2 ≤ (p + 1) + 2) a).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ (p + 1) + 2) (le_max_left _ _))
  obtain ⟨label, hlabel⟩ := hfreeze E EF
    (D.filtration.polynomialSlowBound_mono D.basis w Tbox hT hinput E hE)
    (F.polynomialSlowBound_mono c w Tbox hT hinput EF hEF) hproj
  refine ⟨label, ?_⟩
  intro j v hv hvj
  apply (hlabel j v hv hvj).trans
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2)
    (by linarith : p + 2 ≤ (p + 1) + 2) u)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def FiniteMarkedRationalFactorFreezing
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (B : ℝ) : Prop :=
  ∃ M m n : ℕ, 0 < M ∧ 0 < m ∧ 0 < n ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    ∃ center : Fin n → D.RealGroup,
      (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (center a) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (center a).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (center a).coord ∈ realDenominatorGrid m) ∧
      ∀ (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        ∃ label : (σ → ZMod M) → Fin n,
          ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
            D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R) =
              center (label (fun j => (x j : ZMod M))) * γ ∧
            D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) R =
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                  (D.filtration.filteredRealPolynomialSection F w S hS RF) *
                center (label (fun j => (x j : ZMod M))) * γ

theorem MarkedSlowFactorFreezing.mono_bound
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {Tbox : σ → ℝ} {A ε B B' : ℝ}
    (h : D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox A ε B) (hBB' : B ≤ B') :
    D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox A ε B' := by
  obtain ⟨N, Q, hN, hQ, hNc, hQc, center, hmark, hcap, hfreeze⟩ := h
  exact ⟨N, Q, hN, hQ, hNc.trans hBB', hQc.trans hBB', center, hmark,
    fun j i => (hcap j i).trans hBB', hfreeze⟩

theorem exists_uniform_finite_marked_factor_parameters (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.FiniteMarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) ∧
            D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨A, hA, hparams⟩ := exists_uniform_marked_factor_parameters s a u
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let P := U + (X + U + 2) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hboth⟩ := hparams D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT
  obtain ⟨hrat, hslow⟩ := hboth l hl hlp Tbox hT
  let q := p + (p + A) ^ A
  have hAp : 0 ≤ (p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_add_of_nonneg_right hAp
  have hAq : (p + A) ^ A ≤ q := le_add_of_nonneg_left hp
  have hbud : (p + A) ^ A + (q + 2) ^ 3 ≤ (p + C) ^ C := by
    simpa [P, U, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hAcap : (p + A) ^ A ≤ (p + C) ^ C := by
    have : 0 ≤ (q + 2) ^ 3 := by positivity
    linarith
  have hqcap : (q + 2) ^ 3 ≤ (p + C) ^ C := by linarith
  have hBB : Real.exp ((p + A) ^ A) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hAcap
  refine ⟨?_, hslow.mono_bound hBB⟩
  obtain ⟨M, m, n, hM, hm, hn, hMb, hmb, hnb, center, hcenter, hfac⟩ :=
    MarkedRationalFactorFreezing.finite_enumeration D F c φ hφ w S hS l hq
      (hD.1.trans hpq) (Real.exp_le_exp.mpr hAq) hrat
  exact ⟨M, m, n, hM, hm, hn, hMb.trans hBB, hmb.trans hBB,
    hnb.trans (Real.exp_le_exp.mpr hqcap), center,
    fun j => ⟨(hcenter j).1, fun i => ((hcenter j).2.1 i).trans hBB, (hcenter j).2.2⟩, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
