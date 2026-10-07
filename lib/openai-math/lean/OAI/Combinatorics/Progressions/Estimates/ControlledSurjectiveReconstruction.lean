import OAI.Combinatorics.Progressions.Dynamics.ReconstructionBudget
import OAI.Combinatorics.Progressions.Lattices.FilteredLatticePowerIndex

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem exists_sharp_normal_cover (e : Basis ι ℚ L) (Γ Λ₀ : Subgroup F.Group)
    (l m₀ : ℕ) (hl : 0 < l) (hm₀ : 0 < m₀)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (htarget : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀) :
    ∃ Λ : Subgroup F.Group,
      Λ ≤ Λ₀ ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
      (Λ.subgroupOf Γ).FiniteIndex ∧ Λ.relIndex Γ ≤ (l * m₀) ^ Fintype.card ι ∧
      scaledIntegerGrid ((l * m₀) * l) ⊆ bchSubgroupCoordinates e Λ ∧
      bchSubgroupCoordinates e Λ ⊆ denominatorGrid ((l * m₀) * l) := by
  let m := l * m₀
  obtain ⟨hfinite, hindex⟩ := F.subgroupPowerCover_index_le e Γ l hl houter m
    (Nat.mul_pos hl hm₀)
  exact ⟨subgroupPowerCover Γ m,
    subgroupPowerCover_le_of_grid e Γ Λ₀ l m₀ m houter htarget dvd_rfl,
    subgroupPowerCover_le Γ m, inferInstance, inferInstance, hfinite, hindex,
    subgroupPowerCover_grid e Γ l m hinner houter⟩

theorem exists_normal_cover_exp_quadratic (e : Basis ι ℚ L) (Γ Λ₀ : Subgroup F.Group)
    (l m₀ : ℕ) (hl : 0 < l) (hm₀ : 0 < m₀)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (htarget : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hlb : (l : ℝ) ≤ Real.exp p) (hm₀b : (m₀ : ℝ) ≤ Real.exp p) :
    ∃ Λ : Subgroup F.Group,
      Λ ≤ Λ₀ ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
      (Λ.subgroupOf Γ).FiniteIndex ∧ (Λ.relIndex Γ : ℝ) ≤ Real.exp (2 * p ^ 2) ∧
      ∃ ℓ : ℕ, 0 < ℓ ∧ (ℓ : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
        scaledIntegerGrid ℓ ⊆ bchSubgroupCoordinates e Λ ∧
        bchSubgroupCoordinates e Λ ⊆ denominatorGrid ℓ := by
  obtain ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, hindex, hin, hout⟩ :=
    F.exists_sharp_normal_cover e Γ Λ₀ l m₀ hl hm₀ hinner houter htarget
  refine ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, ?_, (l * m₀) * l,
    Nat.mul_pos (Nat.mul_pos hl hm₀) hl, powerCover_grid_allowance_le_exp l m₀ hp hlb hm₀b,
    hin, hout⟩
  exact (Nat.cast_le.mpr hindex).trans (powerCover_index_allowance_le_exp l m₀ _ hp hlb hm₀b hd)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_surjective_reconstruction_cover (F : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (hφ : Function.Surjective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (Δ : Subgroup F.Group)
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΓout : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΔin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Δ)
    (hΔout : bchSubgroupCoordinates f Δ ⊆ denominatorGrid m)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (p : ℝ) (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hn : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) (hmp : (m : ℝ) ≤ Real.exp p) :
    ∃ Λ : Subgroup F.Group, Λ ≤ Γ.map (NilpotentLieBCHGroup.map φ) ∧ Λ ≤ Δ ∧
      (Λ.subgroupOf Δ).Characteristic ∧ (Λ.subgroupOf Δ).Normal ∧ (Λ.subgroupOf Δ).FiniteIndex ∧
      (Λ.relIndex Δ : ℝ) ≤ Real.exp (2 * ((p + 2) ^ 9) ^ 2) ∧
      ∃ m' : ℕ, 0 < m' ∧ (m' : ℝ) ≤ Real.exp (((p + 2) ^ 9 + 2) ^ 2) ∧
        scaledIntegerGrid m' ⊆ bchSubgroupCoordinates f Λ ∧
        bchSubgroupCoordinates f Λ ⊆ denominatorGrid m' := by
  classical
  obtain ⟨N, hN, hNb, hNin, _⟩ := exists_bchSubgroup_map_grid_exp_bound e f φ hφ Γ hH hl
    (by intro i j; rw [LinearMap.toMatrix_apply]; exact hentries i j)
    hΓin hΓout hp hd hn hHp hlp
  have hpq : p ≤ (p + 2) ^ 9 := le_power_budget hp (by decide)
  have hexp := Real.exp_le_exp.mpr hpq
  exact F.exists_normal_cover_exp_quadratic f Δ (Γ.map (NilpotentLieBCHGroup.map φ)) m N hm hN
    hΔin hΔout hNin (by positivity) (hn.trans hpq) (hmp.trans hexp) hNb

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_controlled_surjective_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι κ L M E : Type*} [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] [NormedAddCommGroup E]
      (F : NilpotentLieFiltration M s) (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (_hφ : Function.Surjective φ)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (Δ : Subgroup F.Group)
      (l m H : ℕ) (hl : 0 < l) (_hm : 0 < m) (_hH : 1 ≤ H)
      (_hΓin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (hΓout : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
      (_hΔin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Δ)
      (_hΔout : bchSubgroupCoordinates f Δ ⊆ denominatorGrid m),
      (∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) →
      (∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H) →
      ∀ (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
        Γ.map realificationHom) → E),
      (∀ k ∈ (realificationMap (hnil := hL) (hM := F.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
        u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
      ∀ (ℓ B : ℝ≥0),
      (letI := realificationQuotientMetricSpace e Γ l hl hΓout; LipschitzWith ℓ u) →
      (∀ x, ‖u x‖ ≤ B) → ∀ (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p → (m : ℝ) ≤ Real.exp p →
      (ℓ : ℝ) ≤ Real.exp p → (B : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup F.Group, Λ ≤ Δ ∧
        Λ ≤ Γ.map (map (hM := F.lowerCentralSeries_eq_bot) φ) ∧
        (Λ.subgroupOf Δ).Characteristic ∧ (Λ.subgroupOf Δ).Normal ∧ (Λ.subgroupOf Δ).FiniteIndex ∧
        (Λ.relIndex Δ : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (m' : ℕ) (hm' : 0 < m') (hout : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m'),
          (m' : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ scaledIntegerGrid m' ⊆ bchSubgroupCoordinates f Λ ∧
          letI := realificationQuotientMetricSpace f Λ m' hm' hout
          ∃ (v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s
            (realification_lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot) ⧸
            Λ.map realificationHom) → E) (K : ℝ≥0),
            (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ LipschitzWith K v ∧ (∀ y, ‖v y‖ ≤ B) ∧
            ∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL)
              (hM := F.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨N, hN, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp s
  let C := N + 22
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro ι κ L M E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F hL e f φ hφ Γ Δ l m H hl hm hH
    hΓin hΓout hΔin hΔout hentries hstructure u hker ℓ B hu hub p hp hd hn hHp hlp hmp hℓp hBp
  obtain ⟨Λ, hcover, hΛ, hchar, hnormal, hfinite, hindex, m', hm', hmb, hmin, hmout⟩ :=
    F.exists_surjective_reconstruction_cover e f φ hφ Γ Δ l m H hl hm hH
      hΓin hΓout hΔin hΔout hentries p hp hd hn hHp hlp hmp
  have h22 : (p + 2) ^ 22 ≤ (p + C) ^ C := by
    have hC : (22 : ℝ) ≤ C := by exact_mod_cast (show 22 ≤ C by dsimp [C]; omega)
    apply (pow_le_pow_left₀ (by linarith) (show p + 2 ≤ p + C by linarith) 22).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hidx : 2 * ((p + 2) ^ 9) ^ 2 ≤ (p + C) ^ C := by
    apply le_trans _ h22
    calc
      2 * ((p + 2) ^ 9) ^ 2 ≤ (p + 2) * (p + 2) ^ 18 := by
        rw [← pow_mul]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (p + 2) ^ 19 := by ring
      _ ≤ (p + 2) ^ 22 := pow_le_pow_right₀ (by linarith) (by decide)
  have hgrid : ((p + 2) ^ 9 + 2) ^ 2 ≤ (p + C) ^ C :=
    (shifted_power_budget_le hp 9 2).trans h22
  refine ⟨Λ, hΛ, hcover, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hidx), m', hm', hmout,
    hmb.trans (Real.exp_le_exp.mpr hgrid), hmin, ?_⟩
  let := realificationQuotientMetricSpace f Λ m' hm' hmout
  obtain ⟨v, hv, hLip, hbound⟩ := exists_lipschitz_realification_reconstruction e f φ hφ Γ Λ hcover
    l m' H hl hm' hH hΓout hmout hentries hstructure u hker ℓ B hu hub
  refine ⟨v, rationalReconstructionLipschitzBound s (Fintype.card ι) (Fintype.card κ) H ℓ B,
    ?_, hLip, hbound, hv⟩
  apply (hcost _ _ _ ℓ B p hp hd hn hHp hℓp hBp).trans
  exact Real.exp_le_exp.mpr (shifted_power_self_mono hp (by omega : 1 ≤ N) (by dsimp [C]; omega))

end Erdos3

end

end OAI
